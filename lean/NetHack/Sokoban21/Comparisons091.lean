/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons090
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c12740 (pattern : Twelve) (guard : d1865 pattern = 1) : d96 pattern ≤ (1 : Int) + d2091 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d96, d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12730 pattern childGuard
    simpa only [d96, d2091, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d96, d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12739 pattern childGuard
    simpa only [d96, d2091, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12741 (pattern : Twelve) (guard : d1865 pattern = 1) : d104 pattern ≤ (1 : Int) + d2092 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d104, d2092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12725 pattern childGuard
    simpa only [d104, d2092, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d104, d2092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12740 pattern childGuard
    simpa only [d104, d2092, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12742 (pattern : Twelve) (guard : d1865 pattern = 1) : d105 pattern ≤ (1 : Int) + d2093 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d105, d2093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12717 pattern childGuard
    simpa only [d105, d2093, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d105, d2093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d105, d2093, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12743 (pattern : Twelve) (guard : d1865 pattern = 1) : d111 pattern ≤ (1 : Int) + d2094 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d111, d2094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12741 pattern childGuard
    simpa only [d111, d2094, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d111, d2094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12742 pattern childGuard
    simpa only [d111, d2094, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12744 (pattern : Twelve) (guard : d1865 pattern = 1) : d114 pattern ≤ (1 : Int) + d2095 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d114, d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12719 pattern childGuard
    simpa only [d114, d2095, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d114, d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12743 pattern childGuard
    simpa only [d114, d2095, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12745 (pattern : Twelve) (guard : d1865 pattern = 1) : d120 pattern ≤ (1 : Int) + d2096 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d120, d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12676 pattern childGuard
    simpa only [d120, d2096, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d120, d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12736 pattern childGuard
    simpa only [d120, d2096, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12746 (pattern : Twelve) (guard : d1865 pattern = 1) : d129 pattern ≤ (1 : Int) + d2097 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d129, d2097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12745 pattern childGuard
    simpa only [d129, d2097, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d129, d2097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12688 pattern childGuard
    simpa only [d129, d2097, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12747 (pattern : Twelve) (guard : d1865 pattern = 1) : d136 pattern ≤ (1 : Int) + d2098 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d136, d2098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12208 pattern childGuard
    simpa only [d136, d2098, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d136, d2098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12746 pattern childGuard
    simpa only [d136, d2098, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12748 (pattern : Twelve) (guard : d1865 pattern = 1) : d144 pattern ≤ (1 : Int) + d2099 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d144, d2099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12680 pattern childGuard
    simpa only [d144, d2099, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d144, d2099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12747 pattern childGuard
    simpa only [d144, d2099, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12749 (pattern : Twelve) (guard : d1865 pattern = 1) : d121 pattern ≤ (1 : Int) + d2100 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d121, d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12208 pattern childGuard
    simpa only [d121, d2100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d121, d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12704 pattern childGuard
    simpa only [d121, d2100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12750 (pattern : Twelve) (guard : d1865 pattern = 1) : d130 pattern ≤ (1 : Int) + d2101 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d130, d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12749 pattern childGuard
    simpa only [d130, d2101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d130, d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12713 pattern childGuard
    simpa only [d130, d2101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12751 (pattern : Twelve) (guard : d1865 pattern = 1) : d137 pattern ≤ (1 : Int) + d2102 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d137, d2102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12696 pattern childGuard
    simpa only [d137, d2102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d137, d2102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12750 pattern childGuard
    simpa only [d137, d2102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12752 (pattern : Twelve) (guard : d1865 pattern = 1) : d138 pattern ≤ (1 : Int) + d2103 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d138, d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12712 pattern childGuard
    simpa only [d138, d2103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d138, d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12746 pattern childGuard
    simpa only [d138, d2103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12753 (pattern : Twelve) (guard : d1865 pattern = 1) : d145 pattern ≤ (1 : Int) + d2104 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d145, d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12751 pattern childGuard
    simpa only [d145, d2104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d145, d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12752 pattern childGuard
    simpa only [d145, d2104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12754 (pattern : Twelve) (guard : d1865 pattern = 1) : d149 pattern ≤ (1 : Int) + d2105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d149, d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12748 pattern childGuard
    simpa only [d149, d2105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d149, d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12753 pattern childGuard
    simpa only [d149, d2105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12755 (pattern : Twelve) (guard : d1865 pattern = 1) : d139 pattern ≤ (1 : Int) + d2106 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d139, d2106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12712 pattern childGuard
    simpa only [d139, d2106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d139, d2106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12750 pattern childGuard
    simpa only [d139, d2106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12756 (pattern : Twelve) (guard : d1865 pattern = 1) : d146 pattern ≤ (1 : Int) + d2107 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d146, d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12755 pattern childGuard
    simpa only [d146, d2107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d146, d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12752 pattern childGuard
    simpa only [d146, d2107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12757 (pattern : Twelve) (guard : d1865 pattern = 1) : d150 pattern ≤ (1 : Int) + d2108 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d150, d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12748 pattern childGuard
    simpa only [d150, d2108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d150, d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12756 pattern childGuard
    simpa only [d150, d2108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12758 (pattern : Twelve) (guard : d1865 pattern = 1) : d153 pattern ≤ (1 : Int) + d2109 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d153, d2109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12754 pattern childGuard
    simpa only [d153, d2109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d153, d2109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12757 pattern childGuard
    simpa only [d153, d2109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12759 (pattern : Twelve) (guard : d1865 pattern = 1) : d4 pattern ≤ (1 : Int) + d4 pattern := by
  omega
theorem c12760 (pattern : Twelve) (guard : d1865 pattern = 1) : d122 pattern ≤ (1 : Int) + d2110 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d122, d2110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12676 pattern childGuard
    simpa only [d122, d2110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d122, d2110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12759 pattern childGuard
    simpa only [d122, d2110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12761 (pattern : Twelve) (guard : d1865 pattern = 1) : d131 pattern ≤ (1 : Int) + d2111 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d131, d2111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12749 pattern childGuard
    simpa only [d131, d2111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d131, d2111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12760 pattern childGuard
    simpa only [d131, d2111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12762 (pattern : Twelve) (guard : d1865 pattern = 1) : d140 pattern ≤ (1 : Int) + d2112 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d140, d2112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12692 pattern childGuard
    simpa only [d140, d2112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d140, d2112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12761 pattern childGuard
    simpa only [d140, d2112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12763 (pattern : Twelve) (guard : d1865 pattern = 1) : d132 pattern ≤ (1 : Int) + d132 pattern := by
  omega
theorem c12764 (pattern : Twelve) (guard : d1865 pattern = 1) : d141 pattern ≤ (1 : Int) + d2113 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d141, d2113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12763 pattern childGuard
    simpa only [d141, d2113, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d141, d2113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12746 pattern childGuard
    simpa only [d141, d2113, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12765 (pattern : Twelve) (guard : d1865 pattern = 1) : d147 pattern ≤ (1 : Int) + d2114 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d147, d2114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12762 pattern childGuard
    simpa only [d147, d2114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d147, d2114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12764 pattern childGuard
    simpa only [d147, d2114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12766 (pattern : Twelve) (guard : d1865 pattern = 1) : d2 pattern ≤ (1 : Int) + d2 pattern := by
  omega
theorem c12767 (pattern : Twelve) (guard : d1865 pattern = 1) : d118 pattern ≤ (1 : Int) + d14 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12426 pattern childGuard
    simpa only [d1865, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12697 pattern childGuard
    simpa only [d1865, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12768 (pattern : Twelve) (guard : d1865 pattern = 1) : d124 pattern ≤ (1 : Int) + d2115 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d124, d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12766 pattern childGuard
    simpa only [d124, d2115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d124, d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12767 pattern childGuard
    simpa only [d124, d2115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12769 (pattern : Twelve) (guard : d0 pattern = 1) : d117 pattern ≤ (1 : Int) + d117 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12770 (pattern : Twelve) (guard : d1865 pattern = 1) : d119 pattern ≤ (1 : Int) + d117 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11268 pattern childGuard
    simpa only [d1865, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12769 pattern childGuard
    simpa only [d1865, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12771 (pattern : Twelve) (guard : d1865 pattern = 1) : d125 pattern ≤ (1 : Int) + d2116 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d125, d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12770 pattern childGuard
    simpa only [d125, d2116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d125, d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d125, d2116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12772 (pattern : Twelve) (guard : d1865 pattern = 1) : d133 pattern ≤ (1 : Int) + d2117 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d133, d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12768 pattern childGuard
    simpa only [d133, d2117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d133, d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12771 pattern childGuard
    simpa only [d133, d2117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12773 (pattern : Twelve) (guard : d1865 pattern = 1) : d142 pattern ≤ (1 : Int) + d2118 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d142, d2118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12726 pattern childGuard
    simpa only [d142, d2118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d142, d2118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12772 pattern childGuard
    simpa only [d142, d2118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12774 (pattern : Twelve) (guard : d1865 pattern = 1) : d134 pattern ≤ (1 : Int) + d134 pattern := by
  omega
theorem c12775 (pattern : Twelve) (guard : d1865 pattern = 1) : d127 pattern ≤ (1 : Int) + d2084 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d127, d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12704 pattern childGuard
    simpa only [d127, d2084, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d127, d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12267 pattern childGuard
    simpa only [d127, d2084, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12776 (pattern : Twelve) (guard : d1865 pattern = 1) : d128 pattern ≤ (1 : Int) + d2119 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d128, d2119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12694 pattern childGuard
    simpa only [d128, d2119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d128, d2119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d128, d2119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12777 (pattern : Twelve) (guard : d1865 pattern = 1) : d135 pattern ≤ (1 : Int) + d2120 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d135, d2120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12775 pattern childGuard
    simpa only [d135, d2120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d135, d2120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12776 pattern childGuard
    simpa only [d135, d2120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12778 (pattern : Twelve) (guard : d1865 pattern = 1) : d143 pattern ≤ (1 : Int) + d2121 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d143, d2121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12774 pattern childGuard
    simpa only [d143, d2121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d143, d2121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12777 pattern childGuard
    simpa only [d143, d2121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12779 (pattern : Twelve) (guard : d1865 pattern = 1) : d148 pattern ≤ (1 : Int) + d2122 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d148, d2122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12773 pattern childGuard
    simpa only [d148, d2122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d148, d2122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12778 pattern childGuard
    simpa only [d148, d2122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12780 (pattern : Twelve) (guard : d1865 pattern = 1) : d151 pattern ≤ (1 : Int) + d2123 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d151, d2123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12765 pattern childGuard
    simpa only [d151, d2123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d151, d2123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12779 pattern childGuard
    simpa only [d151, d2123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12781 (pattern : Twelve) (guard : d1865 pattern = 1) : d152 pattern ≤ (1 : Int) + d2124 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d152, d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12756 pattern childGuard
    simpa only [d152, d2124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d152, d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d152, d2124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12782 (pattern : Twelve) (guard : d1865 pattern = 1) : d154 pattern ≤ (1 : Int) + d2125 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d154, d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12780 pattern childGuard
    simpa only [d154, d2125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d154, d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12781 pattern childGuard
    simpa only [d154, d2125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12783 (pattern : Twelve) (guard : d1865 pattern = 1) : d155 pattern ≤ (1 : Int) + d2126 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d155, d2126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12758 pattern childGuard
    simpa only [d155, d2126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d155, d2126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12782 pattern childGuard
    simpa only [d155, d2126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12784 (pattern : Twelve) (guard : d1865 pattern = 1) : d156 pattern ≤ (1 : Int) + d2127 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d156, d2127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12744 pattern childGuard
    simpa only [d156, d2127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d156, d2127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12783 pattern childGuard
    simpa only [d156, d2127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12785 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (1 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12786 (pattern : Twelve) (guard : d1865 pattern = 1) : d814 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12052 pattern childGuard
    simpa only [d1865, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12785 pattern childGuard
    simpa only [d1865, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12787 (pattern : Twelve) (guard : d1865 pattern = 1) : d816 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12786 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12677 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12788 (pattern : Twelve) (guard : d1865 pattern = 1) : d824 pattern ≤ (1 : Int) + d2128 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d824, d2128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12678 pattern childGuard
    simpa only [d824, d2128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d824, d2128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12787 pattern childGuard
    simpa only [d824, d2128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12789 (pattern : Twelve) (guard : d1865 pattern = 1) : d838 pattern ≤ (1 : Int) + d2129 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d838, d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12208 pattern childGuard
    simpa only [d838, d2129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d838, d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12788 pattern childGuard
    simpa only [d838, d2129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12790 (pattern : Twelve) (guard : d1865 pattern = 1) : d817 pattern ≤ (1 : Int) + d2130 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d817, d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12687 pattern childGuard
    simpa only [d817, d2130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d817, d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12736 pattern childGuard
    simpa only [d817, d2130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12791 (pattern : Twelve) (guard : d1865 pattern = 1) : d825 pattern ≤ (1 : Int) + d2131 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d825, d2131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12790 pattern childGuard
    simpa only [d825, d2131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d825, d2131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12737 pattern childGuard
    simpa only [d825, d2131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12792 (pattern : Twelve) (guard : d1865 pattern = 1) : d839 pattern ≤ (1 : Int) + d2132 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d839, d2132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12676 pattern childGuard
    simpa only [d839, d2132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d839, d2132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12791 pattern childGuard
    simpa only [d839, d2132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12793 (pattern : Twelve) (guard : d1865 pattern = 1) : d853 pattern ≤ (1 : Int) + d2133 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d853, d2133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12789 pattern childGuard
    simpa only [d853, d2133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d853, d2133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12792 pattern childGuard
    simpa only [d853, d2133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12794 (pattern : Twelve) (guard : d1865 pattern = 1) : d818 pattern ≤ (1 : Int) + d45 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d818, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12786 pattern childGuard
    simpa only [d818, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d818, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d818, d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12795 (pattern : Twelve) (guard : d1865 pattern = 1) : d826 pattern ≤ (1 : Int) + d2134 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d826, d2134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12705 pattern childGuard
    simpa only [d826, d2134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d826, d2134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12794 pattern childGuard
    simpa only [d826, d2134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12796 (pattern : Twelve) (guard : d1865 pattern = 1) : d840 pattern ≤ (1 : Int) + d2135 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d840, d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12712 pattern childGuard
    simpa only [d840, d2135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d840, d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12795 pattern childGuard
    simpa only [d840, d2135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12797 (pattern : Twelve) (guard : d1865 pattern = 1) : d827 pattern ≤ (1 : Int) + d2136 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d827, d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12705 pattern childGuard
    simpa only [d827, d2136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d827, d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12713 pattern childGuard
    simpa only [d827, d2136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12798 (pattern : Twelve) (guard : d1865 pattern = 1) : d841 pattern ≤ (1 : Int) + d2137 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d841, d2137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12797 pattern childGuard
    simpa only [d841, d2137, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d841, d2137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12791 pattern childGuard
    simpa only [d841, d2137, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12799 (pattern : Twelve) (guard : d1865 pattern = 1) : d854 pattern ≤ (1 : Int) + d2138 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d854, d2138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12796 pattern childGuard
    simpa only [d854, d2138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d854, d2138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12798 pattern childGuard
    simpa only [d854, d2138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12800 (pattern : Twelve) (guard : d1865 pattern = 1) : d861 pattern ≤ (1 : Int) + d2139 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d861, d2139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12793 pattern childGuard
    simpa only [d861, d2139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d861, d2139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12799 pattern childGuard
    simpa only [d861, d2139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12801 (pattern : Twelve) (guard : d1865 pattern = 1) : d819 pattern ≤ (1 : Int) + d46 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d819, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12786 pattern childGuard
    simpa only [d819, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d819, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12720 pattern childGuard
    simpa only [d819, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12802 (pattern : Twelve) (guard : d1865 pattern = 1) : d828 pattern ≤ (1 : Int) + d2140 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d828, d2140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12705 pattern childGuard
    simpa only [d828, d2140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d828, d2140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12801 pattern childGuard
    simpa only [d828, d2140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12803 (pattern : Twelve) (guard : d1865 pattern = 1) : d842 pattern ≤ (1 : Int) + d2141 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d842, d2141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12692 pattern childGuard
    simpa only [d842, d2141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d842, d2141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12802 pattern childGuard
    simpa only [d842, d2141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12804 (pattern : Twelve) (guard : d1865 pattern = 1) : d843 pattern ≤ (1 : Int) + d2142 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d843, d2142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12705 pattern childGuard
    simpa only [d843, d2142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d843, d2142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12791 pattern childGuard
    simpa only [d843, d2142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12805 (pattern : Twelve) (guard : d1865 pattern = 1) : d855 pattern ≤ (1 : Int) + d2143 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d855, d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12803 pattern childGuard
    simpa only [d855, d2143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d855, d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12804 pattern childGuard
    simpa only [d855, d2143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12806 (pattern : Twelve) (guard : d0 pattern = 1) : d3 pattern ≤ (1 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12807 (pattern : Twelve) (guard : d1865 pattern = 1) : d815 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12069 pattern childGuard
    simpa only [d1865, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12806 pattern childGuard
    simpa only [d1865, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12808 (pattern : Twelve) (guard : d1865 pattern = 1) : d820 pattern ≤ (1 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d820, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12807 pattern childGuard
    simpa only [d820, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d820, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d820, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12809 (pattern : Twelve) (guard : d1865 pattern = 1) : d829 pattern ≤ (1 : Int) + d2144 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d829, d2144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12733 pattern childGuard
    simpa only [d829, d2144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d829, d2144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12808 pattern childGuard
    simpa only [d829, d2144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12810 (pattern : Twelve) (guard : d1865 pattern = 1) : d844 pattern ≤ (1 : Int) + d2145 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d844, d2145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12726 pattern childGuard
    simpa only [d844, d2145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d844, d2145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12809 pattern childGuard
    simpa only [d844, d2145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12811 (pattern : Twelve) (guard : d1865 pattern = 1) : d830 pattern ≤ (1 : Int) + d2146 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d830, d2146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12733 pattern childGuard
    simpa only [d830, d2146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d830, d2146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12728 pattern childGuard
    simpa only [d830, d2146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12812 (pattern : Twelve) (guard : d1865 pattern = 1) : d821 pattern ≤ (1 : Int) + d2147 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d821, d2147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12736 pattern childGuard
    simpa only [d821, d2147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d821, d2147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12698 pattern childGuard
    simpa only [d821, d2147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12813 (pattern : Twelve) (guard : d1865 pattern = 1) : d822 pattern ≤ (1 : Int) + d2148 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d822, d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12698 pattern childGuard
    simpa only [d822, d2148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d822, d2148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d822, d2148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12814 (pattern : Twelve) (guard : d1865 pattern = 1) : d831 pattern ≤ (1 : Int) + d2149 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d831, d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12812 pattern childGuard
    simpa only [d831, d2149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d831, d2149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12813 pattern childGuard
    simpa only [d831, d2149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12815 (pattern : Twelve) (guard : d1865 pattern = 1) : d845 pattern ≤ (1 : Int) + d2150 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d845, d2150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12811 pattern childGuard
    simpa only [d845, d2150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d845, d2150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12814 pattern childGuard
    simpa only [d845, d2150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12816 (pattern : Twelve) (guard : d1865 pattern = 1) : d856 pattern ≤ (1 : Int) + d2151 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d856, d2151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12810 pattern childGuard
    simpa only [d856, d2151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d856, d2151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12815 pattern childGuard
    simpa only [d856, d2151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12817 (pattern : Twelve) (guard : d1865 pattern = 1) : d862 pattern ≤ (1 : Int) + d2152 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d862, d2152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12805 pattern childGuard
    simpa only [d862, d2152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d862, d2152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12816 pattern childGuard
    simpa only [d862, d2152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12818 (pattern : Twelve) (guard : d1865 pattern = 1) : d863 pattern ≤ (1 : Int) + d2153 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d863, d2153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12799 pattern childGuard
    simpa only [d863, d2153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d863, d2153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d863, d2153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12819 (pattern : Twelve) (guard : d1865 pattern = 1) : d867 pattern ≤ (1 : Int) + d2154 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d867, d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12817 pattern childGuard
    simpa only [d867, d2154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d867, d2154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12818 pattern childGuard
    simpa only [d867, d2154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12820 (pattern : Twelve) (guard : d1865 pattern = 1) : d869 pattern ≤ (1 : Int) + d2155 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d869, d2155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12800 pattern childGuard
    simpa only [d869, d2155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d869, d2155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12819 pattern childGuard
    simpa only [d869, d2155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12821 (pattern : Twelve) (guard : d0 pattern = 1) : d8 pattern ≤ (1 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c12822 (pattern : Twelve) (guard : d1865 pattern = 1) : d872 pattern ≤ (1 : Int) + d8 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11214 pattern childGuard
    simpa only [d1865, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12821 pattern childGuard
    simpa only [d1865, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12823 (pattern : Twelve) (guard : d1865 pattern = 1) : d874 pattern ≤ (1 : Int) + d2156 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d874, d2156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12676 pattern childGuard
    simpa only [d874, d2156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d874, d2156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12822 pattern childGuard
    simpa only [d874, d2156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12824 (pattern : Twelve) (guard : d1865 pattern = 1) : d875 pattern ≤ (1 : Int) + d2157 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d875, d2157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12786 pattern childGuard
    simpa only [d875, d2157, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d875, d2157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12822 pattern childGuard
    simpa only [d875, d2157, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12825 (pattern : Twelve) (guard : d1865 pattern = 1) : d882 pattern ≤ (1 : Int) + d2158 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d882, d2158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12823 pattern childGuard
    simpa only [d882, d2158, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d882, d2158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12824 pattern childGuard
    simpa only [d882, d2158, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12826 (pattern : Twelve) (guard : d1865 pattern = 1) : d890 pattern ≤ (1 : Int) + d2159 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d890, d2159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12208 pattern childGuard
    simpa only [d890, d2159, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d890, d2159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12825 pattern childGuard
    simpa only [d890, d2159, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12827 (pattern : Twelve) (guard : d1865 pattern = 1) : d876 pattern ≤ (1 : Int) + d2160 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d876, d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12687 pattern childGuard
    simpa only [d876, d2160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d876, d2160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12698 pattern childGuard
    simpa only [d876, d2160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12828 (pattern : Twelve) (guard : d1865 pattern = 1) : d883 pattern ≤ (1 : Int) + d2161 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d883, d2161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12827 pattern childGuard
    simpa only [d883, d2161, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d883, d2161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12737 pattern childGuard
    simpa only [d883, d2161, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12829 (pattern : Twelve) (guard : d1865 pattern = 1) : d891 pattern ≤ (1 : Int) + d2162 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d891, d2162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12676 pattern childGuard
    simpa only [d891, d2162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d891, d2162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12828 pattern childGuard
    simpa only [d891, d2162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12830 (pattern : Twelve) (guard : d1865 pattern = 1) : d898 pattern ≤ (1 : Int) + d2163 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d898, d2163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12826 pattern childGuard
    simpa only [d898, d2163, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d898, d2163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12829 pattern childGuard
    simpa only [d898, d2163, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12831 (pattern : Twelve) (guard : d1865 pattern = 1) : d877 pattern ≤ (1 : Int) + d2079 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d877, d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12676 pattern childGuard
    simpa only [d877, d2079, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d877, d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12807 pattern childGuard
    simpa only [d877, d2079, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12832 (pattern : Twelve) (guard : d1865 pattern = 1) : d884 pattern ≤ (1 : Int) + d2164 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d884, d2164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12831 pattern childGuard
    simpa only [d884, d2164, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d884, d2164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12794 pattern childGuard
    simpa only [d884, d2164, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12833 (pattern : Twelve) (guard : d1865 pattern = 1) : d892 pattern ≤ (1 : Int) + d2165 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d892, d2165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12712 pattern childGuard
    simpa only [d892, d2165, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d892, d2165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12832 pattern childGuard
    simpa only [d892, d2165, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12834 (pattern : Twelve) (guard : d1865 pattern = 1) : d893 pattern ≤ (1 : Int) + d2166 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d893, d2166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12797 pattern childGuard
    simpa only [d893, d2166, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d893, d2166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12828 pattern childGuard
    simpa only [d893, d2166, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12835 (pattern : Twelve) (guard : d1865 pattern = 1) : d899 pattern ≤ (1 : Int) + d2167 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d899, d2167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12833 pattern childGuard
    simpa only [d899, d2167, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d899, d2167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12834 pattern childGuard
    simpa only [d899, d2167, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12836 (pattern : Twelve) (guard : d1865 pattern = 1) : d902 pattern ≤ (1 : Int) + d2168 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d902, d2168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12830 pattern childGuard
    simpa only [d902, d2168, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d902, d2168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12835 pattern childGuard
    simpa only [d902, d2168, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12837 (pattern : Twelve) (guard : d1865 pattern = 1) : d878 pattern ≤ (1 : Int) + d2169 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d878, d2169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12786 pattern childGuard
    simpa only [d878, d2169, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d878, d2169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12732 pattern childGuard
    simpa only [d878, d2169, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12838 (pattern : Twelve) (guard : d1865 pattern = 1) : d885 pattern ≤ (1 : Int) + d2170 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d885, d2170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12831 pattern childGuard
    simpa only [d885, d2170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d885, d2170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12837 pattern childGuard
    simpa only [d885, d2170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12839 (pattern : Twelve) (guard : d1865 pattern = 1) : d894 pattern ≤ (1 : Int) + d2171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d894, d2171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12692 pattern childGuard
    simpa only [d894, d2171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d894, d2171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12838 pattern childGuard
    simpa only [d894, d2171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12840 (pattern : Twelve) (guard : d1865 pattern = 1) : d879 pattern ≤ (1 : Int) + d2172 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d879, d2172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12676 pattern childGuard
    simpa only [d879, d2172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d879, d2172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12770 pattern childGuard
    simpa only [d879, d2172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12841 (pattern : Twelve) (guard : d1865 pattern = 1) : d886 pattern ≤ (1 : Int) + d2173 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d886, d2173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12705 pattern childGuard
    simpa only [d886, d2173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d886, d2173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12840 pattern childGuard
    simpa only [d886, d2173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12842 (pattern : Twelve) (guard : d1865 pattern = 1) : d895 pattern ≤ (1 : Int) + d2174 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d895, d2174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12841 pattern childGuard
    simpa only [d895, d2174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d895, d2174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12828 pattern childGuard
    simpa only [d895, d2174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12843 (pattern : Twelve) (guard : d1865 pattern = 1) : d900 pattern ≤ (1 : Int) + d2175 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d900, d2175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12839 pattern childGuard
    simpa only [d900, d2175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d900, d2175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12842 pattern childGuard
    simpa only [d900, d2175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12844 (pattern : Twelve) (guard : d1865 pattern = 1) : d873 pattern ≤ (1 : Int) + d15 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12543 pattern childGuard
    simpa only [d1865, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12731 pattern childGuard
    simpa only [d1865, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12845 (pattern : Twelve) (guard : d1865 pattern = 1) : d880 pattern ≤ (1 : Int) + d2176 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d880, d2176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12844 pattern childGuard
    simpa only [d880, d2176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d880, d2176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d880, d2176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12846 (pattern : Twelve) (guard : d1865 pattern = 1) : d887 pattern ≤ (1 : Int) + d2177 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d887, d2177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12775 pattern childGuard
    simpa only [d887, d2177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d887, d2177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12845 pattern childGuard
    simpa only [d887, d2177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12847 (pattern : Twelve) (guard : d1865 pattern = 1) : d896 pattern ≤ (1 : Int) + d2178 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d896, d2178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12726 pattern childGuard
    simpa only [d896, d2178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d896, d2178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12846 pattern childGuard
    simpa only [d896, d2178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12848 (pattern : Twelve) (guard : d1865 pattern = 1) : d881 pattern ≤ (1 : Int) + d2179 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d881, d2179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12704 pattern childGuard
    simpa only [d881, d2179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d881, d2179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12767 pattern childGuard
    simpa only [d881, d2179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12849 (pattern : Twelve) (guard : d1865 pattern = 1) : d888 pattern ≤ (1 : Int) + d2180 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d888, d2180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12848 pattern childGuard
    simpa only [d888, d2180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d888, d2180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12771 pattern childGuard
    simpa only [d888, d2180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12850 (pattern : Twelve) (guard : d1865 pattern = 1) : d889 pattern ≤ (1 : Int) + d2181 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d889, d2181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12737 pattern childGuard
    simpa only [d889, d2181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d889, d2181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d889, d2181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12851 (pattern : Twelve) (guard : d1865 pattern = 1) : d897 pattern ≤ (1 : Int) + d2182 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d897, d2182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12849 pattern childGuard
    simpa only [d897, d2182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d897, d2182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12850 pattern childGuard
    simpa only [d897, d2182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12852 (pattern : Twelve) (guard : d1865 pattern = 1) : d901 pattern ≤ (1 : Int) + d2183 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d901, d2183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12847 pattern childGuard
    simpa only [d901, d2183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d901, d2183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12851 pattern childGuard
    simpa only [d901, d2183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12853 (pattern : Twelve) (guard : d1865 pattern = 1) : d903 pattern ≤ (1 : Int) + d2184 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d903, d2184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12843 pattern childGuard
    simpa only [d903, d2184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d903, d2184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12852 pattern childGuard
    simpa only [d903, d2184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12854 (pattern : Twelve) (guard : d1865 pattern = 1) : d904 pattern ≤ (1 : Int) + d2185 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d904, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12835 pattern childGuard
    simpa only [d904, d2185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d904, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d904, d2185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12855 (pattern : Twelve) (guard : d1865 pattern = 1) : d905 pattern ≤ (1 : Int) + d2186 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d905, d2186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12853 pattern childGuard
    simpa only [d905, d2186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d905, d2186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12854 pattern childGuard
    simpa only [d905, d2186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12856 (pattern : Twelve) (guard : d1865 pattern = 1) : d906 pattern ≤ (1 : Int) + d2187 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d906, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12836 pattern childGuard
    simpa only [d906, d2187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d906, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12855 pattern childGuard
    simpa only [d906, d2187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12857 (pattern : Twelve) (guard : d1865 pattern = 1) : d907 pattern ≤ (1 : Int) + d2188 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d907, d2188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12820 pattern childGuard
    simpa only [d907, d2188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d907, d2188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12856 pattern childGuard
    simpa only [d907, d2188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12858 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (1 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11060 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11213 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12859 (pattern : Twelve) (guard : d1865 pattern = 1) : d1275 pattern ≤ (1 : Int) + d8 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12858 pattern childGuard
    simpa only [d1865, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12821 pattern childGuard
    simpa only [d1865, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12860 (pattern : Twelve) (guard : d1865 pattern = 1) : d1278 pattern ≤ (1 : Int) + d8 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12859 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12822 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12861 (pattern : Twelve) (guard : d1865 pattern = 1) : d1284 pattern ≤ (1 : Int) + d8 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12860 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12822 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12862 (pattern : Twelve) (guard : d1865 pattern = 1) : d1293 pattern ≤ (1 : Int) + d2189 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1293, d2189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12676 pattern childGuard
    simpa only [d1293, d2189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1293, d2189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12861 pattern childGuard
    simpa only [d1293, d2189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12863 (pattern : Twelve) (guard : d1865 pattern = 1) : d1294 pattern ≤ (1 : Int) + d2190 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1294, d2190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12687 pattern childGuard
    simpa only [d1294, d2190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1294, d2190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1294, d2190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12864 (pattern : Twelve) (guard : d1865 pattern = 1) : d1305 pattern ≤ (1 : Int) + d2191 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1305, d2191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12862 pattern childGuard
    simpa only [d1305, d2191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1305, d2191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12863 pattern childGuard
    simpa only [d1305, d2191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12865 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (1 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11137 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11267 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12866 (pattern : Twelve) (guard : d1865 pattern = 1) : d1276 pattern ≤ (1 : Int) + d117 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12865 pattern childGuard
    simpa only [d1865, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12769 pattern childGuard
    simpa only [d1865, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12867 (pattern : Twelve) (guard : d1865 pattern = 1) : d1279 pattern ≤ (1 : Int) + d2192 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1279, d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12859 pattern childGuard
    simpa only [d1279, d2192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1279, d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12866 pattern childGuard
    simpa only [d1279, d2192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12868 (pattern : Twelve) (guard : d1865 pattern = 1) : d1280 pattern ≤ (1 : Int) + d2193 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1280, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12822 pattern childGuard
    simpa only [d1280, d2193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1280, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1280, d2193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12869 (pattern : Twelve) (guard : d1865 pattern = 1) : d1285 pattern ≤ (1 : Int) + d2194 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1285, d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12867 pattern childGuard
    simpa only [d1285, d2194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1285, d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12868 pattern childGuard
    simpa only [d1285, d2194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12870 (pattern : Twelve) (guard : d1865 pattern = 1) : d1295 pattern ≤ (1 : Int) + d2195 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1295, d2195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12797 pattern childGuard
    simpa only [d1295, d2195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1295, d2195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12869 pattern childGuard
    simpa only [d1295, d2195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12871 (pattern : Twelve) (guard : d1865 pattern = 1) : d1286 pattern ≤ (1 : Int) + d2196 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1286, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12790 pattern childGuard
    simpa only [d1286, d2196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1286, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12688 pattern childGuard
    simpa only [d1286, d2196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12872 (pattern : Twelve) (guard : d1865 pattern = 1) : d1296 pattern ≤ (1 : Int) + d2197 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1296, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12871 pattern childGuard
    simpa only [d1296, d2197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1296, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1296, d2197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12873 (pattern : Twelve) (guard : d1865 pattern = 1) : d1306 pattern ≤ (1 : Int) + d2198 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1306, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12870 pattern childGuard
    simpa only [d1306, d2198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1306, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12872 pattern childGuard
    simpa only [d1306, d2198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12874 (pattern : Twelve) (guard : d1865 pattern = 1) : d1313 pattern ≤ (1 : Int) + d2199 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1313, d2199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12864 pattern childGuard
    simpa only [d1313, d2199, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1313, d2199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12873 pattern childGuard
    simpa only [d1313, d2199, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12875 (pattern : Twelve) (guard : d1865 pattern = 1) : d1281 pattern ≤ (1 : Int) + d2192 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1281, d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12822 pattern childGuard
    simpa only [d1281, d2192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1281, d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12770 pattern childGuard
    simpa only [d1281, d2192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12876 (pattern : Twelve) (guard : d1865 pattern = 1) : d1287 pattern ≤ (1 : Int) + d2192 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12867 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12875 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12877 (pattern : Twelve) (guard : d1865 pattern = 1) : d1297 pattern ≤ (1 : Int) + d2200 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1297, d2200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12705 pattern childGuard
    simpa only [d1297, d2200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1297, d2200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12876 pattern childGuard
    simpa only [d1297, d2200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12878 (pattern : Twelve) (guard : d1865 pattern = 1) : d1298 pattern ≤ (1 : Int) + d2201 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1298, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12790 pattern childGuard
    simpa only [d1298, d2201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1298, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1298, d2201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12879 (pattern : Twelve) (guard : d1865 pattern = 1) : d1307 pattern ≤ (1 : Int) + d2202 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1307, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12877 pattern childGuard
    simpa only [d1307, d2202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1307, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12878 pattern childGuard
    simpa only [d1307, d2202, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
