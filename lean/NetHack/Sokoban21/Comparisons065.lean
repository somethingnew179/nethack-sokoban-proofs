/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons064
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c9100 (pattern : Twelve) (guard : d1848 pattern = 1) : d1675 pattern ≤ (0 : Int) + d1724 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1675, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9097 pattern childGuard
    simpa only [d1675, d1724, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1675, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9099 pattern childGuard
    simpa only [d1675, d1724, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9101 (pattern : Twelve) (guard : d1848 pattern = 1) : d1676 pattern ≤ (0 : Int) + d1726 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1676, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9100 pattern childGuard
    simpa only [d1676, d1726, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1676, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9088 pattern childGuard
    simpa only [d1676, d1726, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9102 (pattern : Twelve) (guard : d1848 pattern = 1) : d1677 pattern ≤ (0 : Int) + d1728 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1677, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9093 pattern childGuard
    simpa only [d1677, d1728, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1677, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9101 pattern childGuard
    simpa only [d1677, d1728, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9103 (pattern : Twelve) (guard : d1848 pattern = 1) : d1678 pattern ≤ (0 : Int) + d1729 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1678, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9090 pattern childGuard
    simpa only [d1678, d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1678, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9102 pattern childGuard
    simpa only [d1678, d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9104 (pattern : Twelve) (guard : d0 pattern = 1) : d51 pattern ≤ (0 : Int) + d186 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9105 (pattern : Twelve) (guard : d1852 pattern = 1) : d73 pattern ≤ (0 : Int) + d426 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d73, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d73, d426, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d73, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9104 pattern childGuard
    simpa only [d1852, d73, d426, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9106 (pattern : Twelve) (guard : d1852 pattern = 1) : d91 pattern ≤ (0 : Int) + d444 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d91, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2177 pattern childGuard
    simpa only [d91, d444, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d91, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9105 pattern childGuard
    simpa only [d91, d444, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9107 (pattern : Twelve) (guard : d0 pattern = 1) : d55 pattern ≤ (0 : Int) + d189 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9108 (pattern : Twelve) (guard : d1852 pattern = 1) : d75 pattern ≤ (0 : Int) + d428 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d75, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6339 pattern childGuard
    simpa only [d1852, d75, d428, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d75, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9107 pattern childGuard
    simpa only [d1852, d75, d428, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9109 (pattern : Twelve) (guard : d1852 pattern = 1) : d92 pattern ≤ (0 : Int) + d445 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d92, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2182 pattern childGuard
    simpa only [d92, d445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d92, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9108 pattern childGuard
    simpa only [d92, d445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9110 (pattern : Twelve) (guard : d1852 pattern = 1) : d102 pattern ≤ (0 : Int) + d455 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d102, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9106 pattern childGuard
    simpa only [d102, d455, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d102, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9109 pattern childGuard
    simpa only [d102, d455, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9111 (pattern : Twelve) (guard : d1852 pattern = 1) : d76 pattern ≤ (0 : Int) + d430 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d76, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d76, d430, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d76, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9107 pattern childGuard
    simpa only [d1852, d76, d430, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9112 (pattern : Twelve) (guard : d1852 pattern = 1) : d93 pattern ≤ (0 : Int) + d446 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d93, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2187 pattern childGuard
    simpa only [d93, d446, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d93, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9111 pattern childGuard
    simpa only [d93, d446, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9113 (pattern : Twelve) (guard : d0 pattern = 1) : d55 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9114 (pattern : Twelve) (guard : d1852 pattern = 1) : d78 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d78, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d78, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d78, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9113 pattern childGuard
    simpa only [d1852, d78, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9115 (pattern : Twelve) (guard : d1852 pattern = 1) : d94 pattern ≤ (0 : Int) + d447 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d94, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2192 pattern childGuard
    simpa only [d94, d447, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d94, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9114 pattern childGuard
    simpa only [d94, d447, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9116 (pattern : Twelve) (guard : d1852 pattern = 1) : d103 pattern ≤ (0 : Int) + d456 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d103, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9112 pattern childGuard
    simpa only [d103, d456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d103, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9115 pattern childGuard
    simpa only [d103, d456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9117 (pattern : Twelve) (guard : d1852 pattern = 1) : d110 pattern ≤ (0 : Int) + d465 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d110, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9110 pattern childGuard
    simpa only [d110, d465, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d110, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9116 pattern childGuard
    simpa only [d110, d465, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9118 (pattern : Twelve) (guard : d0 pattern = 1) : d55 pattern ≤ (0 : Int) + d194 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9119 (pattern : Twelve) (guard : d1852 pattern = 1) : d80 pattern ≤ (0 : Int) + d434 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d80, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d80, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d80, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9118 pattern childGuard
    simpa only [d1852, d80, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9120 (pattern : Twelve) (guard : d1852 pattern = 1) : d95 pattern ≤ (0 : Int) + d448 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d95, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2198 pattern childGuard
    simpa only [d95, d448, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d95, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9119 pattern childGuard
    simpa only [d95, d448, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9121 (pattern : Twelve) (guard : d0 pattern = 1) : d61 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9122 (pattern : Twelve) (guard : d1852 pattern = 1) : d82 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d82, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2201 pattern childGuard
    simpa only [d1852, d82, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d82, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9121 pattern childGuard
    simpa only [d1852, d82, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9123 (pattern : Twelve) (guard : d1852 pattern = 1) : d96 pattern ≤ (0 : Int) + d449 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d96, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2203 pattern childGuard
    simpa only [d96, d449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d96, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9122 pattern childGuard
    simpa only [d96, d449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9124 (pattern : Twelve) (guard : d1852 pattern = 1) : d104 pattern ≤ (0 : Int) + d457 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d104, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9120 pattern childGuard
    simpa only [d104, d457, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d104, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9123 pattern childGuard
    simpa only [d104, d457, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9125 (pattern : Twelve) (guard : d1852 pattern = 1) : d94 pattern ≤ (0 : Int) + d450 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d94, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2208 pattern childGuard
    simpa only [d94, d450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d94, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9114 pattern childGuard
    simpa only [d94, d450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9126 (pattern : Twelve) (guard : d1852 pattern = 1) : d105 pattern ≤ (0 : Int) + d458 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d105, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9125 pattern childGuard
    simpa only [d105, d458, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d105, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6359 pattern childGuard
    simpa only [d105, d458, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9127 (pattern : Twelve) (guard : d1852 pattern = 1) : d111 pattern ≤ (0 : Int) + d466 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d111, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9124 pattern childGuard
    simpa only [d111, d466, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d111, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9126 pattern childGuard
    simpa only [d111, d466, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9128 (pattern : Twelve) (guard : d1852 pattern = 1) : d114 pattern ≤ (0 : Int) + d471 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d114, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9117 pattern childGuard
    simpa only [d114, d471, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d114, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9127 pattern childGuard
    simpa only [d114, d471, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9129 (pattern : Twelve) (guard : d0 pattern = 1) : d51 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9130 (pattern : Twelve) (guard : d1852 pattern = 1) : d73 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d73, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d73, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d73, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9129 pattern childGuard
    simpa only [d1852, d73, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9131 (pattern : Twelve) (guard : d1852 pattern = 1) : d91 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2216 pattern childGuard
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9130 pattern childGuard
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9132 (pattern : Twelve) (guard : d1852 pattern = 1) : d75 pattern ≤ (0 : Int) + d440 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d75, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6339 pattern childGuard
    simpa only [d1852, d75, d440, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d75, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9113 pattern childGuard
    simpa only [d1852, d75, d440, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9133 (pattern : Twelve) (guard : d1852 pattern = 1) : d92 pattern ≤ (0 : Int) + d451 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d92, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2244 pattern childGuard
    simpa only [d92, d451, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d92, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9132 pattern childGuard
    simpa only [d92, d451, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9134 (pattern : Twelve) (guard : d1852 pattern = 1) : d102 pattern ≤ (0 : Int) + d459 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d102, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9131 pattern childGuard
    simpa only [d102, d459, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d102, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9133 pattern childGuard
    simpa only [d102, d459, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9135 (pattern : Twelve) (guard : d1852 pattern = 1) : d76 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d76, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d76, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d76, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9113 pattern childGuard
    simpa only [d1852, d76, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9136 (pattern : Twelve) (guard : d1852 pattern = 1) : d93 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2216 pattern childGuard
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9135 pattern childGuard
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9137 (pattern : Twelve) (guard : d1852 pattern = 1) : d94 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2248 pattern childGuard
    simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9114 pattern childGuard
    simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9138 (pattern : Twelve) (guard : d1852 pattern = 1) : d103 pattern ≤ (0 : Int) + d460 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d103, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9136 pattern childGuard
    simpa only [d103, d460, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d103, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9137 pattern childGuard
    simpa only [d103, d460, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9139 (pattern : Twelve) (guard : d1852 pattern = 1) : d110 pattern ≤ (0 : Int) + d467 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d110, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9134 pattern childGuard
    simpa only [d110, d467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d110, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9138 pattern childGuard
    simpa only [d110, d467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9140 (pattern : Twelve) (guard : d1852 pattern = 1) : d80 pattern ≤ (0 : Int) + d441 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d80, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d80, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d80, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9113 pattern childGuard
    simpa only [d1852, d80, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9141 (pattern : Twelve) (guard : d1852 pattern = 1) : d95 pattern ≤ (0 : Int) + d441 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2253 pattern childGuard
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9140 pattern childGuard
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9142 (pattern : Twelve) (guard : d1852 pattern = 1) : d96 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2256 pattern childGuard
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9122 pattern childGuard
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9143 (pattern : Twelve) (guard : d1852 pattern = 1) : d104 pattern ≤ (0 : Int) + d461 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d104, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9141 pattern childGuard
    simpa only [d104, d461, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d104, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9142 pattern childGuard
    simpa only [d104, d461, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9144 (pattern : Twelve) (guard : d1852 pattern = 1) : d105 pattern ≤ (0 : Int) + d462 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d105, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9137 pattern childGuard
    simpa only [d105, d462, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d105, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6359 pattern childGuard
    simpa only [d105, d462, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9145 (pattern : Twelve) (guard : d1852 pattern = 1) : d111 pattern ≤ (0 : Int) + d468 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d111, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9143 pattern childGuard
    simpa only [d111, d468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d111, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9144 pattern childGuard
    simpa only [d111, d468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9146 (pattern : Twelve) (guard : d1852 pattern = 1) : d114 pattern ≤ (0 : Int) + d472 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d114, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9139 pattern childGuard
    simpa only [d114, d472, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d114, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9145 pattern childGuard
    simpa only [d114, d472, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9147 (pattern : Twelve) (guard : d1852 pattern = 1) : d114 pattern ≤ (0 : Int) + d474 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9128 pattern childGuard
    simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9146 pattern childGuard
    simpa only [d474, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9148 (pattern : Twelve) (guard : d1852 pattern = 1) : d114 pattern ≤ (0 : Int) + d475 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9147 pattern childGuard
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9146 pattern childGuard
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9149 (pattern : Twelve) (guard : d0 pattern = 1) : d129 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9150 (pattern : Twelve) (guard : d1852 pattern = 1) : d136 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d136, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d136, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d136, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9149 pattern childGuard
    simpa only [d1852, d136, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9151 (pattern : Twelve) (guard : d1852 pattern = 1) : d144 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2216 pattern childGuard
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9150 pattern childGuard
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9152 (pattern : Twelve) (guard : d0 pattern = 1) : d130 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9153 (pattern : Twelve) (guard : d1852 pattern = 1) : d137 pattern ≤ (0 : Int) + d439 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d137, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2180 pattern childGuard
    simpa only [d1852, d137, d439, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d137, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9152 pattern childGuard
    simpa only [d1852, d137, d439, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9154 (pattern : Twelve) (guard : d1852 pattern = 1) : d138 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d138, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d138, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d138, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9149 pattern childGuard
    simpa only [d1852, d138, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9155 (pattern : Twelve) (guard : d1852 pattern = 1) : d145 pattern ≤ (0 : Int) + d452 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d145, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9153 pattern childGuard
    simpa only [d145, d452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d145, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9154 pattern childGuard
    simpa only [d145, d452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9156 (pattern : Twelve) (guard : d1852 pattern = 1) : d149 pattern ≤ (0 : Int) + d463 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d149, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9151 pattern childGuard
    simpa only [d149, d463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d149, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9155 pattern childGuard
    simpa only [d149, d463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9157 (pattern : Twelve) (guard : d1852 pattern = 1) : d139 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d139, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d139, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d139, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9152 pattern childGuard
    simpa only [d1852, d139, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9158 (pattern : Twelve) (guard : d1852 pattern = 1) : d146 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9157 pattern childGuard
    simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9154 pattern childGuard
    simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9159 (pattern : Twelve) (guard : d1852 pattern = 1) : d150 pattern ≤ (0 : Int) + d460 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d150, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9151 pattern childGuard
    simpa only [d150, d460, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d150, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9158 pattern childGuard
    simpa only [d150, d460, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9160 (pattern : Twelve) (guard : d1852 pattern = 1) : d153 pattern ≤ (0 : Int) + d469 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d153, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9156 pattern childGuard
    simpa only [d153, d469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d153, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9159 pattern childGuard
    simpa only [d153, d469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9161 (pattern : Twelve) (guard : d0 pattern = 1) : d131 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9162 (pattern : Twelve) (guard : d1852 pattern = 1) : d140 pattern ≤ (0 : Int) + d441 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d140, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d140, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d140, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9161 pattern childGuard
    simpa only [d1852, d140, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9163 (pattern : Twelve) (guard : d1852 pattern = 1) : d141 pattern ≤ (0 : Int) + d442 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d141, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6397 pattern childGuard
    simpa only [d1852, d141, d442, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d141, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9149 pattern childGuard
    simpa only [d1852, d141, d442, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9164 (pattern : Twelve) (guard : d1852 pattern = 1) : d147 pattern ≤ (0 : Int) + d453 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d147, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9162 pattern childGuard
    simpa only [d147, d453, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d147, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9163 pattern childGuard
    simpa only [d147, d453, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9165 (pattern : Twelve) (guard : d0 pattern = 1) : d133 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9166 (pattern : Twelve) (guard : d1852 pattern = 1) : d142 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d142, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2201 pattern childGuard
    simpa only [d1852, d142, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d142, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9165 pattern childGuard
    simpa only [d1852, d142, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9167 (pattern : Twelve) (guard : d0 pattern = 1) : d135 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9168 (pattern : Twelve) (guard : d1852 pattern = 1) : d143 pattern ≤ (0 : Int) + d443 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d143, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6402 pattern childGuard
    simpa only [d1852, d143, d443, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d143, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9167 pattern childGuard
    simpa only [d1852, d143, d443, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9169 (pattern : Twelve) (guard : d1852 pattern = 1) : d148 pattern ≤ (0 : Int) + d454 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d148, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9166 pattern childGuard
    simpa only [d148, d454, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d148, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9168 pattern childGuard
    simpa only [d148, d454, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9170 (pattern : Twelve) (guard : d1852 pattern = 1) : d151 pattern ≤ (0 : Int) + d464 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d151, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9164 pattern childGuard
    simpa only [d151, d464, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d151, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9169 pattern childGuard
    simpa only [d151, d464, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9171 (pattern : Twelve) (guard : d1852 pattern = 1) : d152 pattern ≤ (0 : Int) + d462 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d152, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9158 pattern childGuard
    simpa only [d152, d462, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d152, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6359 pattern childGuard
    simpa only [d152, d462, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9172 (pattern : Twelve) (guard : d1852 pattern = 1) : d154 pattern ≤ (0 : Int) + d470 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d154, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9170 pattern childGuard
    simpa only [d154, d470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d154, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9171 pattern childGuard
    simpa only [d154, d470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9173 (pattern : Twelve) (guard : d1852 pattern = 1) : d155 pattern ≤ (0 : Int) + d473 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d155, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9160 pattern childGuard
    simpa only [d155, d473, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d155, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9172 pattern childGuard
    simpa only [d155, d473, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9174 (pattern : Twelve) (guard : d1852 pattern = 1) : d156 pattern ≤ (0 : Int) + d476 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d156, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9148 pattern childGuard
    simpa only [d156, d476, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d156, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9173 pattern childGuard
    simpa only [d156, d476, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9175 (pattern : Twelve) (guard : d0 pattern = 1) : d825 pattern ≤ (0 : Int) + d908 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9176 (pattern : Twelve) (guard : d1852 pattern = 1) : d839 pattern ≤ (0 : Int) + d1070 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d839, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1852, d839, d1070, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d839, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9175 pattern childGuard
    simpa only [d1852, d839, d1070, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9177 (pattern : Twelve) (guard : d1852 pattern = 1) : d853 pattern ≤ (0 : Int) + d1078 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d853, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2285 pattern childGuard
    simpa only [d853, d1078, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d853, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9176 pattern childGuard
    simpa only [d853, d1078, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9178 (pattern : Twelve) (guard : d0 pattern = 1) : d825 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9179 (pattern : Twelve) (guard : d1852 pattern = 1) : d841 pattern ≤ (0 : Int) + d1072 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d841, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2361 pattern childGuard
    simpa only [d1852, d841, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d841, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9178 pattern childGuard
    simpa only [d1852, d841, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9180 (pattern : Twelve) (guard : d1852 pattern = 1) : d854 pattern ≤ (0 : Int) + d1079 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d854, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2289 pattern childGuard
    simpa only [d854, d1079, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d854, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9179 pattern childGuard
    simpa only [d854, d1079, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9181 (pattern : Twelve) (guard : d1852 pattern = 1) : d861 pattern ≤ (0 : Int) + d1088 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d861, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9177 pattern childGuard
    simpa only [d861, d1088, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d861, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9180 pattern childGuard
    simpa only [d861, d1088, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9182 (pattern : Twelve) (guard : d1852 pattern = 1) : d839 pattern ≤ (0 : Int) + d1073 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d839, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1852, d839, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d839, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9178 pattern childGuard
    simpa only [d1852, d839, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9183 (pattern : Twelve) (guard : d1852 pattern = 1) : d853 pattern ≤ (0 : Int) + d1080 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d853, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2294 pattern childGuard
    simpa only [d853, d1080, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d853, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9182 pattern childGuard
    simpa only [d853, d1080, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9184 (pattern : Twelve) (guard : d1852 pattern = 1) : d854 pattern ≤ (0 : Int) + d1081 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d854, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2298 pattern childGuard
    simpa only [d854, d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d854, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9179 pattern childGuard
    simpa only [d854, d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9185 (pattern : Twelve) (guard : d1852 pattern = 1) : d861 pattern ≤ (0 : Int) + d1089 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d861, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9183 pattern childGuard
    simpa only [d861, d1089, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d861, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9184 pattern childGuard
    simpa only [d861, d1089, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9186 (pattern : Twelve) (guard : d1852 pattern = 1) : d861 pattern ≤ (0 : Int) + d1095 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9181 pattern childGuard
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9185 pattern childGuard
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9187 (pattern : Twelve) (guard : d1852 pattern = 1) : d843 pattern ≤ (0 : Int) + d1074 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d843, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1852, d843, d1074, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d843, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9178 pattern childGuard
    simpa only [d1852, d843, d1074, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9188 (pattern : Twelve) (guard : d1852 pattern = 1) : d855 pattern ≤ (0 : Int) + d1082 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d855, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2304 pattern childGuard
    simpa only [d855, d1082, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d855, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9187 pattern childGuard
    simpa only [d855, d1082, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9189 (pattern : Twelve) (guard : d0 pattern = 1) : d831 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9190 (pattern : Twelve) (guard : d1852 pattern = 1) : d845 pattern ≤ (0 : Int) + d1075 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d845, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2374 pattern childGuard
    simpa only [d1852, d845, d1075, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d845, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9189 pattern childGuard
    simpa only [d1852, d845, d1075, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9191 (pattern : Twelve) (guard : d1852 pattern = 1) : d856 pattern ≤ (0 : Int) + d1083 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d856, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2308 pattern childGuard
    simpa only [d856, d1083, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d856, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9190 pattern childGuard
    simpa only [d856, d1083, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9192 (pattern : Twelve) (guard : d1852 pattern = 1) : d862 pattern ≤ (0 : Int) + d1090 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d862, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9188 pattern childGuard
    simpa only [d862, d1090, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d862, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9191 pattern childGuard
    simpa only [d862, d1090, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9193 (pattern : Twelve) (guard : d1852 pattern = 1) : d863 pattern ≤ (0 : Int) + d1091 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d863, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9184 pattern childGuard
    simpa only [d863, d1091, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d863, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6359 pattern childGuard
    simpa only [d863, d1091, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9194 (pattern : Twelve) (guard : d1852 pattern = 1) : d867 pattern ≤ (0 : Int) + d1096 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d867, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9192 pattern childGuard
    simpa only [d867, d1096, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d867, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9193 pattern childGuard
    simpa only [d867, d1096, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9195 (pattern : Twelve) (guard : d1852 pattern = 1) : d869 pattern ≤ (0 : Int) + d1099 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d869, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9186 pattern childGuard
    simpa only [d869, d1099, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d869, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9194 pattern childGuard
    simpa only [d869, d1099, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9196 (pattern : Twelve) (guard : d1852 pattern = 1) : d853 pattern ≤ (0 : Int) + d1084 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d853, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2316 pattern childGuard
    simpa only [d853, d1084, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d853, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9182 pattern childGuard
    simpa only [d853, d1084, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9197 (pattern : Twelve) (guard : d1852 pattern = 1) : d861 pattern ≤ (0 : Int) + d1092 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d861, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9196 pattern childGuard
    simpa only [d861, d1092, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d861, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9184 pattern childGuard
    simpa only [d861, d1092, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9198 (pattern : Twelve) (guard : d1852 pattern = 1) : d855 pattern ≤ (0 : Int) + d1085 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d855, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2337 pattern childGuard
    simpa only [d855, d1085, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d855, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9187 pattern childGuard
    simpa only [d855, d1085, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9199 (pattern : Twelve) (guard : d1852 pattern = 1) : d862 pattern ≤ (0 : Int) + d1093 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d862, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9198 pattern childGuard
    simpa only [d862, d1093, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d862, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9191 pattern childGuard
    simpa only [d862, d1093, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9200 (pattern : Twelve) (guard : d1852 pattern = 1) : d867 pattern ≤ (0 : Int) + d1097 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d867, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9199 pattern childGuard
    simpa only [d867, d1097, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d867, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9193 pattern childGuard
    simpa only [d867, d1097, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9201 (pattern : Twelve) (guard : d1852 pattern = 1) : d869 pattern ≤ (0 : Int) + d1100 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d869, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9197 pattern childGuard
    simpa only [d869, d1100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d869, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9200 pattern childGuard
    simpa only [d869, d1100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9202 (pattern : Twelve) (guard : d1852 pattern = 1) : d869 pattern ≤ (0 : Int) + d1102 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9195 pattern childGuard
    simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9201 pattern childGuard
    simpa only [d1102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9203 (pattern : Twelve) (guard : d1852 pattern = 1) : d869 pattern ≤ (0 : Int) + d1103 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9202 pattern childGuard
    simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9201 pattern childGuard
    simpa only [d1103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9204 (pattern : Twelve) (guard : d0 pattern = 1) : d882 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9205 (pattern : Twelve) (guard : d1852 pattern = 1) : d890 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d890, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d890, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d890, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9204 pattern childGuard
    simpa only [d1852, d890, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9206 (pattern : Twelve) (guard : d0 pattern = 1) : d883 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9207 (pattern : Twelve) (guard : d1852 pattern = 1) : d891 pattern ≤ (0 : Int) + d1073 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d891, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1852, d891, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d891, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9206 pattern childGuard
    simpa only [d1852, d891, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9208 (pattern : Twelve) (guard : d1852 pattern = 1) : d898 pattern ≤ (0 : Int) + d1084 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d898, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9205 pattern childGuard
    simpa only [d898, d1084, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d898, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9207 pattern childGuard
    simpa only [d898, d1084, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9209 (pattern : Twelve) (guard : d0 pattern = 1) : d884 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9210 (pattern : Twelve) (guard : d1852 pattern = 1) : d892 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d892, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d892, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d892, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9209 pattern childGuard
    simpa only [d1852, d892, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9211 (pattern : Twelve) (guard : d1852 pattern = 1) : d893 pattern ≤ (0 : Int) + d1072 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d893, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2361 pattern childGuard
    simpa only [d1852, d893, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d893, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9206 pattern childGuard
    simpa only [d1852, d893, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9212 (pattern : Twelve) (guard : d1852 pattern = 1) : d899 pattern ≤ (0 : Int) + d1081 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d899, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9210 pattern childGuard
    simpa only [d899, d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d899, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9211 pattern childGuard
    simpa only [d899, d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9213 (pattern : Twelve) (guard : d1852 pattern = 1) : d902 pattern ≤ (0 : Int) + d1092 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d902, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9208 pattern childGuard
    simpa only [d902, d1092, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d902, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9212 pattern childGuard
    simpa only [d902, d1092, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9214 (pattern : Twelve) (guard : d0 pattern = 1) : d885 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9215 (pattern : Twelve) (guard : d1852 pattern = 1) : d894 pattern ≤ (0 : Int) + d441 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d894, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d894, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d894, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9214 pattern childGuard
    simpa only [d1852, d894, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9216 (pattern : Twelve) (guard : d1852 pattern = 1) : d895 pattern ≤ (0 : Int) + d1076 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d895, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6452 pattern childGuard
    simpa only [d1852, d895, d1076, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d895, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9206 pattern childGuard
    simpa only [d1852, d895, d1076, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9217 (pattern : Twelve) (guard : d1852 pattern = 1) : d900 pattern ≤ (0 : Int) + d1086 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d900, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9215 pattern childGuard
    simpa only [d900, d1086, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d900, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9216 pattern childGuard
    simpa only [d900, d1086, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9218 (pattern : Twelve) (guard : d0 pattern = 1) : d887 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9219 (pattern : Twelve) (guard : d1852 pattern = 1) : d896 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d896, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2201 pattern childGuard
    simpa only [d1852, d896, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d896, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9218 pattern childGuard
    simpa only [d1852, d896, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9220 (pattern : Twelve) (guard : d1852 pattern = 1) : d897 pattern ≤ (0 : Int) + d1077 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d897, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6457 pattern childGuard
    simpa only [d1852, d897, d1077, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d897, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5403 pattern childGuard
    simpa only [d1852, d897, d1077, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9221 (pattern : Twelve) (guard : d1852 pattern = 1) : d901 pattern ≤ (0 : Int) + d1087 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d901, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9219 pattern childGuard
    simpa only [d901, d1087, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d901, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9220 pattern childGuard
    simpa only [d901, d1087, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9222 (pattern : Twelve) (guard : d1852 pattern = 1) : d903 pattern ≤ (0 : Int) + d1094 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d903, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9217 pattern childGuard
    simpa only [d903, d1094, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d903, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9221 pattern childGuard
    simpa only [d903, d1094, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9223 (pattern : Twelve) (guard : d1852 pattern = 1) : d904 pattern ≤ (0 : Int) + d1091 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d904, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9212 pattern childGuard
    simpa only [d904, d1091, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d904, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6359 pattern childGuard
    simpa only [d904, d1091, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9224 (pattern : Twelve) (guard : d1852 pattern = 1) : d905 pattern ≤ (0 : Int) + d1098 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d905, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9222 pattern childGuard
    simpa only [d905, d1098, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d905, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9223 pattern childGuard
    simpa only [d905, d1098, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9225 (pattern : Twelve) (guard : d1852 pattern = 1) : d906 pattern ≤ (0 : Int) + d1101 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d906, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9213 pattern childGuard
    simpa only [d906, d1101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d906, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9224 pattern childGuard
    simpa only [d906, d1101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9226 (pattern : Twelve) (guard : d1852 pattern = 1) : d907 pattern ≤ (0 : Int) + d1104 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d907, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9203 pattern childGuard
    simpa only [d907, d1104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d907, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9225 pattern childGuard
    simpa only [d907, d1104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9227 (pattern : Twelve) (guard : d1852 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1472 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1305, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2359 pattern childGuard
    simpa only [d1305, d1472, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1305, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6466 pattern childGuard
    simpa only [d1305, d1472, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9228 (pattern : Twelve) (guard : d1852 pattern = 1) : d1306 pattern ≤ (0 : Int) + d1473 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1306, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2363 pattern childGuard
    simpa only [d1306, d1473, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1306, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6468 pattern childGuard
    simpa only [d1306, d1473, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9229 (pattern : Twelve) (guard : d1852 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1479 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1313, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9227 pattern childGuard
    simpa only [d1313, d1479, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1313, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9228 pattern childGuard
    simpa only [d1313, d1479, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9230 (pattern : Twelve) (guard : d1852 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1474 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1305, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2367 pattern childGuard
    simpa only [d1305, d1474, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1305, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6466 pattern childGuard
    simpa only [d1305, d1474, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9231 (pattern : Twelve) (guard : d1852 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1480 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1313, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9230 pattern childGuard
    simpa only [d1313, d1480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1313, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9228 pattern childGuard
    simpa only [d1313, d1480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9232 (pattern : Twelve) (guard : d1852 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1484 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9229 pattern childGuard
    simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9231 pattern childGuard
    simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9233 (pattern : Twelve) (guard : d1852 pattern = 1) : d1307 pattern ≤ (0 : Int) + d1475 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1307, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2372 pattern childGuard
    simpa only [d1307, d1475, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1307, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6474 pattern childGuard
    simpa only [d1307, d1475, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9234 (pattern : Twelve) (guard : d1852 pattern = 1) : d1308 pattern ≤ (0 : Int) + d1476 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1308, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2376 pattern childGuard
    simpa only [d1308, d1476, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1308, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6476 pattern childGuard
    simpa only [d1308, d1476, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9235 (pattern : Twelve) (guard : d1852 pattern = 1) : d1314 pattern ≤ (0 : Int) + d1481 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1314, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9233 pattern childGuard
    simpa only [d1314, d1481, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1314, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9234 pattern childGuard
    simpa only [d1314, d1481, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9236 (pattern : Twelve) (guard : d1852 pattern = 1) : d1315 pattern ≤ (0 : Int) + d1482 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1315, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9228 pattern childGuard
    simpa only [d1315, d1482, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1315, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6359 pattern childGuard
    simpa only [d1315, d1482, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9237 (pattern : Twelve) (guard : d1852 pattern = 1) : d1319 pattern ≤ (0 : Int) + d1485 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1319, d1485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9235 pattern childGuard
    simpa only [d1319, d1485, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1319, d1485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9236 pattern childGuard
    simpa only [d1319, d1485, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9238 (pattern : Twelve) (guard : d1852 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1487 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1321, d1487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9232 pattern childGuard
    simpa only [d1321, d1487, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1321, d1487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9237 pattern childGuard
    simpa only [d1321, d1487, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9239 (pattern : Twelve) (guard : d1852 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1488 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1321, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9231 pattern childGuard
    simpa only [d1321, d1488, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1321, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9237 pattern childGuard
    simpa only [d1321, d1488, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
