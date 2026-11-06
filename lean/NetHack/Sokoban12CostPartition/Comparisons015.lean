/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2100 (p : Pattern) (guard : d798 p = 1) : d347 p ≤ (0 : Int) + d142 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d347, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1787 p hg
    simpa only [d798, d347, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d347, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1486 p hg
    simpa only [d798, d347, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2101 (p : Pattern) (guard : d798 p = 1) : d349 p ≤ (0 : Int) + d149 p := by
  cases selected : p 158 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d798, d349, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1789 p hg
    simpa only [d798, d349, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d798, d349, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1488 p hg
    simpa only [d798, d349, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2102 (p : Pattern) (guard : d798 p = 1) : d350 p ≤ (0 : Int) + d150 p := by
  cases selected : p 141 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d350, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2100 p hg
    simpa only [d350, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d350, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2101 p hg
    simpa only [d350, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2103 (p : Pattern) (guard : d798 p = 1) : d351 p ≤ (0 : Int) + d151 p := by
  cases selected : p 134 with
  | false =>
    have hg : d798 p = 1 := by simpa only [d351, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2102 p hg
    simpa only [d351, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d351, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare511 p hg
    simpa only [d351, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2104 (p : Pattern) (guard : d799 p = 1) : d352 p ≤ (0 : Int) + d152 p := by
  cases selected : p 133 with
  | false =>
    have hg : d794 p = 1 := by simpa only [d799, d352, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1763 p hg
    simpa only [d799, d352, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d799, d352, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2103 p hg
    simpa only [d799, d352, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2105 (p : Pattern) (guard : d0 p = 1) : d354 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2106 (p : Pattern) (guard : d800 p = 1) : d355 p ≤ (0 : Int) + d200 p := by
  cases selected : p 132 with
  | false =>
    have hg : d799 p = 1 := by simpa only [d800, d355, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2104 p hg
    simpa only [d800, d355, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d800, d355, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2105 p hg
    simpa only [d800, d355, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2107 (p : Pattern) (guard : d800 p = 1) : d356 p ≤ (0 : Int) + d201 p := by
  cases selected : p 108 with
  | false =>
    have hg : d800 p = 1 := by simpa only [d356, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2099 p hg
    simpa only [d356, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d800 p = 1 := by simpa only [d356, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2106 p hg
    simpa only [d356, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2108 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2109 (p : Pattern) (guard : d829 p = 1) : d7 p ≤ (0 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d829, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2108 p hg
    simpa only [d829, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2110 (p : Pattern) (guard : d829 p = 1) : d56 p ≤ (0 : Int) + d56 p := by
  omega
theorem compare2111 (p : Pattern) (guard : d829 p = 1) : d57 p ≤ (0 : Int) + d56 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2109 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2110 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2112 (p : Pattern) (guard : d1015 p = 1) : d114 p ≤ (0 : Int) + d56 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1015, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2111 p hg
    simpa only [d1015, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1015, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1656 p hg
    simpa only [d1015, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2113 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (0 : Int) + d60 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2114 (p : Pattern) (guard : d829 p = 1) : d11 p ≤ (0 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare295 p hg
    simpa only [d829, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2113 p hg
    simpa only [d829, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2115 (p : Pattern) (guard : d829 p = 1) : d12 p ≤ (0 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d12, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2109 p hg
    simpa only [d12, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d12, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2114 p hg
    simpa only [d12, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2116 (p : Pattern) (guard : d829 p = 1) : d62 p ≤ (0 : Int) + d62 p := by
  omega
theorem compare2117 (p : Pattern) (guard : d829 p = 1) : d63 p ≤ (0 : Int) + d62 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2115 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2116 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2118 (p : Pattern) (guard : d1015 p = 1) : d116 p ≤ (0 : Int) + d62 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1015, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2117 p hg
    simpa only [d1015, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1015, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1664 p hg
    simpa only [d1015, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2119 (p : Pattern) (guard : d1015 p = 1) : d335 p ≤ (0 : Int) + d451 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d335, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2112 p hg
    simpa only [d335, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d335, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2118 p hg
    simpa only [d335, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2120 (p : Pattern) (guard : d829 p = 1) : d55 p ≤ (0 : Int) + d55 p := by
  omega
theorem compare2121 (p : Pattern) (guard : d829 p = 1) : d106 p ≤ (0 : Int) + d452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d106, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2109 p hg
    simpa only [d106, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d106, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d106, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2122 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d452 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2123 (p : Pattern) (guard : d1015 p = 1) : d107 p ≤ (0 : Int) + d452 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1015, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2121 p hg
    simpa only [d1015, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1015, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2122 p hg
    simpa only [d1015, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2124 (p : Pattern) (guard : d829 p = 1) : d65 p ≤ (0 : Int) + d65 p := by
  omega
theorem compare2125 (p : Pattern) (guard : d829 p = 1) : d109 p ≤ (0 : Int) + d453 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d109, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2115 p hg
    simpa only [d109, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d109, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d109, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2126 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d453 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2127 (p : Pattern) (guard : d1015 p = 1) : d110 p ≤ (0 : Int) + d453 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1015, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2125 p hg
    simpa only [d1015, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1015, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2126 p hg
    simpa only [d1015, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2128 (p : Pattern) (guard : d1015 p = 1) : d336 p ≤ (0 : Int) + d454 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d336, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2123 p hg
    simpa only [d336, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d336, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2127 p hg
    simpa only [d336, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2129 (p : Pattern) (guard : d1015 p = 1) : d337 p ≤ (0 : Int) + d455 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d337, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2119 p hg
    simpa only [d337, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d337, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2128 p hg
    simpa only [d337, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2130 (p : Pattern) (guard : d1015 p = 1) : d55 p ≤ (0 : Int) + d55 p := by
  omega
theorem compare2131 (p : Pattern) (guard : d1015 p = 1) : d338 p ≤ (0 : Int) + d456 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d338, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2112 p hg
    simpa only [d338, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d338, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2130 p hg
    simpa only [d338, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2132 (p : Pattern) (guard : d1015 p = 1) : d65 p ≤ (0 : Int) + d65 p := by
  omega
theorem compare2133 (p : Pattern) (guard : d1015 p = 1) : d339 p ≤ (0 : Int) + d457 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d339, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2118 p hg
    simpa only [d339, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d339, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2132 p hg
    simpa only [d339, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2134 (p : Pattern) (guard : d1015 p = 1) : d340 p ≤ (0 : Int) + d458 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d340, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2131 p hg
    simpa only [d340, d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d340, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2133 p hg
    simpa only [d340, d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2135 (p : Pattern) (guard : d1015 p = 1) : d211 p ≤ (0 : Int) + d459 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d211, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2123 p hg
    simpa only [d211, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d211, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2130 p hg
    simpa only [d211, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2136 (p : Pattern) (guard : d1015 p = 1) : d212 p ≤ (0 : Int) + d460 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d212, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2127 p hg
    simpa only [d212, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d212, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2132 p hg
    simpa only [d212, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2137 (p : Pattern) (guard : d1015 p = 1) : d213 p ≤ (0 : Int) + d461 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d213, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2135 p hg
    simpa only [d213, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d213, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2136 p hg
    simpa only [d213, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2138 (p : Pattern) (guard : d1015 p = 1) : d341 p ≤ (0 : Int) + d462 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d341, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2134 p hg
    simpa only [d341, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d341, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2137 p hg
    simpa only [d341, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2139 (p : Pattern) (guard : d1015 p = 1) : d342 p ≤ (0 : Int) + d463 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d342, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2129 p hg
    simpa only [d342, d463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d342, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2138 p hg
    simpa only [d342, d463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2140 (p : Pattern) (guard : d1015 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare2141 (p : Pattern) (guard : d1015 p = 1) : d343 p ≤ (0 : Int) + d464 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d343, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2138 p hg
    simpa only [d343, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d343, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2140 p hg
    simpa only [d343, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2142 (p : Pattern) (guard : d1015 p = 1) : d344 p ≤ (0 : Int) + d465 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d344, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2139 p hg
    simpa only [d344, d465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d344, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2141 p hg
    simpa only [d344, d465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2143 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d466 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2144 (p : Pattern) (guard : d1015 p = 1) : d114 p ≤ (0 : Int) + d467 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1015, d114, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2111 p hg
    simpa only [d1015, d114, d467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1015, d114, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2143 p hg
    simpa only [d1015, d114, d467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2145 (p : Pattern) (guard : d1015 p = 1) : d114 p ≤ (0 : Int) + d468 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2112 p hg
    simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2144 p hg
    simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2146 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d469 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2147 (p : Pattern) (guard : d1015 p = 1) : d116 p ≤ (0 : Int) + d470 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1015, d116, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2117 p hg
    simpa only [d1015, d116, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1015, d116, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2146 p hg
    simpa only [d1015, d116, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2148 (p : Pattern) (guard : d1015 p = 1) : d116 p ≤ (0 : Int) + d471 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2118 p hg
    simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2147 p hg
    simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2149 (p : Pattern) (guard : d1015 p = 1) : d335 p ≤ (0 : Int) + d472 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d335, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2145 p hg
    simpa only [d335, d472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d335, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2148 p hg
    simpa only [d335, d472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2150 (p : Pattern) (guard : d1015 p = 1) : d345 p ≤ (0 : Int) + d473 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d345, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2149 p hg
    simpa only [d345, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d345, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2140 p hg
    simpa only [d345, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2151 (p : Pattern) (guard : d829 p = 1) : d137 p ≤ (0 : Int) + d137 p := by
  omega
theorem compare2152 (p : Pattern) (guard : d829 p = 1) : d138 p ≤ (0 : Int) + d466 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d138, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2109 p hg
    simpa only [d138, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d138, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2151 p hg
    simpa only [d138, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2153 (p : Pattern) (guard : d1015 p = 1) : d346 p ≤ (0 : Int) + d466 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1015, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2152 p hg
    simpa only [d1015, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1015, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2143 p hg
    simpa only [d1015, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2154 (p : Pattern) (guard : d1015 p = 1) : d347 p ≤ (0 : Int) + d474 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d347, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2153 p hg
    simpa only [d347, d474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d347, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2130 p hg
    simpa only [d347, d474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2155 (p : Pattern) (guard : d829 p = 1) : d144 p ≤ (0 : Int) + d144 p := by
  omega
theorem compare2156 (p : Pattern) (guard : d829 p = 1) : d145 p ≤ (0 : Int) + d469 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d145, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2115 p hg
    simpa only [d145, d469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d145, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2155 p hg
    simpa only [d145, d469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2157 (p : Pattern) (guard : d1015 p = 1) : d348 p ≤ (0 : Int) + d469 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1015, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d1015, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1015, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2146 p hg
    simpa only [d1015, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2158 (p : Pattern) (guard : d1015 p = 1) : d349 p ≤ (0 : Int) + d475 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d349, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2157 p hg
    simpa only [d349, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d349, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2132 p hg
    simpa only [d349, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2159 (p : Pattern) (guard : d1015 p = 1) : d350 p ≤ (0 : Int) + d476 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d350, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2154 p hg
    simpa only [d350, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d350, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2158 p hg
    simpa only [d350, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2160 (p : Pattern) (guard : d1015 p = 1) : d351 p ≤ (0 : Int) + d477 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d351, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2159 p hg
    simpa only [d351, d477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d351, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2140 p hg
    simpa only [d351, d477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2161 (p : Pattern) (guard : d1015 p = 1) : d352 p ≤ (0 : Int) + d478 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d352, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2150 p hg
    simpa only [d352, d478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d352, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2160 p hg
    simpa only [d352, d478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2162 (p : Pattern) (guard : d1015 p = 1) : d338 p ≤ (0 : Int) + d479 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d338, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2144 p hg
    simpa only [d338, d479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d338, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2130 p hg
    simpa only [d338, d479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2163 (p : Pattern) (guard : d1015 p = 1) : d339 p ≤ (0 : Int) + d480 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d339, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2147 p hg
    simpa only [d339, d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d339, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2132 p hg
    simpa only [d339, d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2164 (p : Pattern) (guard : d1015 p = 1) : d340 p ≤ (0 : Int) + d481 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d340, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2162 p hg
    simpa only [d340, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d340, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2163 p hg
    simpa only [d340, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2165 (p : Pattern) (guard : d1015 p = 1) : d353 p ≤ (0 : Int) + d482 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d353, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2164 p hg
    simpa only [d353, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d353, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2140 p hg
    simpa only [d353, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2166 (p : Pattern) (guard : d1015 p = 1) : d354 p ≤ (0 : Int) + d483 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d354, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2165 p hg
    simpa only [d354, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d354, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2140 p hg
    simpa only [d354, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2167 (p : Pattern) (guard : d1015 p = 1) : d355 p ≤ (0 : Int) + d484 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d355, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2161 p hg
    simpa only [d355, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d355, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2166 p hg
    simpa only [d355, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2168 (p : Pattern) (guard : d1015 p = 1) : d356 p ≤ (0 : Int) + d485 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1015 p = 1 := by simpa only [d356, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2142 p hg
    simpa only [d356, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1015 p = 1 := by simpa only [d356, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2167 p hg
    simpa only [d356, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2169 (p : Pattern) (guard : d758 p = 1) : d106 p ≤ (0 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d758, d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1656 p hg
    simpa only [d758, d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2170 (p : Pattern) (guard : d758 p = 1) : d109 p ≤ (0 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare294 p hg
    simpa only [d758, d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1664 p hg
    simpa only [d758, d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2171 (p : Pattern) (guard : d758 p = 1) : d227 p ≤ (0 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d227, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2169 p hg
    simpa only [d227, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d227, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2170 p hg
    simpa only [d227, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2172 (p : Pattern) (guard : d826 p = 1) : d227 p ≤ (0 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d826, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2171 p hg
    simpa only [d826, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d826, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d826, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2173 (p : Pattern) (guard : d758 p = 1) : d229 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d229, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2169 p hg
    simpa only [d229, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d229, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare702 p hg
    simpa only [d229, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2174 (p : Pattern) (guard : d758 p = 1) : d230 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d230, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2170 p hg
    simpa only [d230, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d230, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare704 p hg
    simpa only [d230, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2175 (p : Pattern) (guard : d758 p = 1) : d231 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d231, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2173 p hg
    simpa only [d231, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d231, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2174 p hg
    simpa only [d231, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2176 (p : Pattern) (guard : d826 p = 1) : d231 p ≤ (0 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d826, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2175 p hg
    simpa only [d826, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d826, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare847 p hg
    simpa only [d826, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2177 (p : Pattern) (guard : d826 p = 1) : d366 p ≤ (0 : Int) + d72 p := by
  cases selected : p 133 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d366, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2172 p hg
    simpa only [d366, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d366, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2176 p hg
    simpa only [d366, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2178 (p : Pattern) (guard : d826 p = 1) : d367 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d367, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2176 p hg
    simpa only [d367, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d367, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare757 p hg
    simpa only [d367, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2179 (p : Pattern) (guard : d826 p = 1) : d368 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d368, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2177 p hg
    simpa only [d368, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d368, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2178 p hg
    simpa only [d368, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2180 (p : Pattern) (guard : d826 p = 1) : d369 p ≤ (0 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d826, d369, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2171 p hg
    simpa only [d826, d369, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d826, d369, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d826, d369, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2181 (p : Pattern) (guard : d826 p = 1) : d370 p ≤ (0 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d826, d370, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2175 p hg
    simpa only [d826, d370, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d826, d370, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d826, d370, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2182 (p : Pattern) (guard : d826 p = 1) : d371 p ≤ (0 : Int) + d72 p := by
  cases selected : p 133 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d371, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2180 p hg
    simpa only [d371, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d371, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2181 p hg
    simpa only [d371, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2183 (p : Pattern) (guard : d826 p = 1) : d372 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d372, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2181 p hg
    simpa only [d372, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d372, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare757 p hg
    simpa only [d372, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2184 (p : Pattern) (guard : d826 p = 1) : d373 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d373, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2182 p hg
    simpa only [d373, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d373, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2183 p hg
    simpa only [d373, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2185 (p : Pattern) (guard : d826 p = 1) : d374 p ≤ (0 : Int) + d74 p := by
  cases selected : p 108 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2179 p hg
    simpa only [d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2184 p hg
    simpa only [d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2186 (p : Pattern) (guard : d0 p = 1) : d227 p ≤ (0 : Int) + d64 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2187 (p : Pattern) (guard : d759 p = 1) : d227 p ≤ (0 : Int) + d64 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2186 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2171 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2188 (p : Pattern) (guard : d0 p = 1) : d231 p ≤ (0 : Int) + d70 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2189 (p : Pattern) (guard : d759 p = 1) : d231 p ≤ (0 : Int) + d70 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2188 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2175 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2190 (p : Pattern) (guard : d759 p = 1) : d366 p ≤ (0 : Int) + d811 p := by
  cases selected : p 133 with
  | false =>
    have hg : d759 p = 1 := by simpa only [d366, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2187 p hg
    simpa only [d366, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d759 p = 1 := by simpa only [d366, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2189 p hg
    simpa only [d366, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2191 (p : Pattern) (guard : d759 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare2192 (p : Pattern) (guard : d759 p = 1) : d367 p ≤ (0 : Int) + d812 p := by
  cases selected : p 133 with
  | false =>
    have hg : d759 p = 1 := by simpa only [d367, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2189 p hg
    simpa only [d367, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d759 p = 1 := by simpa only [d367, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2191 p hg
    simpa only [d367, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2193 (p : Pattern) (guard : d759 p = 1) : d368 p ≤ (0 : Int) + d813 p := by
  cases selected : p 132 with
  | false =>
    have hg : d759 p = 1 := by simpa only [d368, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2190 p hg
    simpa only [d368, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d759 p = 1 := by simpa only [d368, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2192 p hg
    simpa only [d368, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2194 (p : Pattern) (guard : d0 p = 1) : d373 p ≤ (0 : Int) + d813 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2195 (p : Pattern) (guard : d760 p = 1) : d374 p ≤ (0 : Int) + d813 p := by
  cases selected : p 108 with
  | false =>
    have hg : d759 p = 1 := by simpa only [d760, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2193 p hg
    simpa only [d760, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d760, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2194 p hg
    simpa only [d760, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2196 (p : Pattern) (guard : d1016 p = 1) : d106 p ≤ (0 : Int) + d56 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2109 p hg
    simpa only [d1016, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1656 p hg
    simpa only [d1016, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2197 (p : Pattern) (guard : d1016 p = 1) : d109 p ≤ (0 : Int) + d62 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2115 p hg
    simpa only [d1016, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1664 p hg
    simpa only [d1016, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2198 (p : Pattern) (guard : d1016 p = 1) : d227 p ≤ (0 : Int) + d451 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d227, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2196 p hg
    simpa only [d227, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d227, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2197 p hg
    simpa only [d227, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2199 (p : Pattern) (guard : d1016 p = 1) : d106 p ≤ (0 : Int) + d452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d106, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2109 p hg
    simpa only [d1016, d106, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d106, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d1016, d106, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2200 (p : Pattern) (guard : d1016 p = 1) : d109 p ≤ (0 : Int) + d453 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d109, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2115 p hg
    simpa only [d1016, d109, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d109, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d1016, d109, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2201 (p : Pattern) (guard : d1016 p = 1) : d227 p ≤ (0 : Int) + d454 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d227, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2199 p hg
    simpa only [d227, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d227, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2200 p hg
    simpa only [d227, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2202 (p : Pattern) (guard : d1016 p = 1) : d227 p ≤ (0 : Int) + d455 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2198 p hg
    simpa only [d455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2201 p hg
    simpa only [d455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2203 (p : Pattern) (guard : d1016 p = 1) : d55 p ≤ (0 : Int) + d55 p := by
  omega
theorem compare2204 (p : Pattern) (guard : d1016 p = 1) : d229 p ≤ (0 : Int) + d456 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d229, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2196 p hg
    simpa only [d229, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d229, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2203 p hg
    simpa only [d229, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2205 (p : Pattern) (guard : d1016 p = 1) : d65 p ≤ (0 : Int) + d65 p := by
  omega
theorem compare2206 (p : Pattern) (guard : d1016 p = 1) : d230 p ≤ (0 : Int) + d457 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d230, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2197 p hg
    simpa only [d230, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d230, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2205 p hg
    simpa only [d230, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2207 (p : Pattern) (guard : d1016 p = 1) : d231 p ≤ (0 : Int) + d458 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d231, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2204 p hg
    simpa only [d231, d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d231, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2206 p hg
    simpa only [d231, d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2208 (p : Pattern) (guard : d1016 p = 1) : d229 p ≤ (0 : Int) + d459 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d229, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2199 p hg
    simpa only [d229, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d229, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2203 p hg
    simpa only [d229, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2209 (p : Pattern) (guard : d1016 p = 1) : d230 p ≤ (0 : Int) + d460 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d230, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2200 p hg
    simpa only [d230, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d230, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2205 p hg
    simpa only [d230, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2210 (p : Pattern) (guard : d1016 p = 1) : d231 p ≤ (0 : Int) + d461 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d231, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2208 p hg
    simpa only [d231, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d231, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2209 p hg
    simpa only [d231, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2211 (p : Pattern) (guard : d1016 p = 1) : d231 p ≤ (0 : Int) + d462 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2207 p hg
    simpa only [d462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2210 p hg
    simpa only [d462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2212 (p : Pattern) (guard : d1016 p = 1) : d366 p ≤ (0 : Int) + d463 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d366, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2202 p hg
    simpa only [d366, d463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d366, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2211 p hg
    simpa only [d366, d463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2213 (p : Pattern) (guard : d1016 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare2214 (p : Pattern) (guard : d1016 p = 1) : d367 p ≤ (0 : Int) + d464 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d367, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2211 p hg
    simpa only [d367, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d367, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2213 p hg
    simpa only [d367, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2215 (p : Pattern) (guard : d1016 p = 1) : d368 p ≤ (0 : Int) + d465 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d368, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2212 p hg
    simpa only [d368, d465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d368, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2214 p hg
    simpa only [d368, d465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2216 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d137 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2217 (p : Pattern) (guard : d1016 p = 1) : d106 p ≤ (0 : Int) + d466 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d106, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2109 p hg
    simpa only [d1016, d106, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d106, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2216 p hg
    simpa only [d1016, d106, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2218 (p : Pattern) (guard : d1016 p = 1) : d106 p ≤ (0 : Int) + d467 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2196 p hg
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2217 p hg
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2219 (p : Pattern) (guard : d1016 p = 1) : d106 p ≤ (0 : Int) + d468 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2196 p hg
    simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2218 p hg
    simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2220 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (0 : Int) + d144 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2221 (p : Pattern) (guard : d1016 p = 1) : d109 p ≤ (0 : Int) + d469 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d109, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2115 p hg
    simpa only [d1016, d109, d469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d109, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2220 p hg
    simpa only [d1016, d109, d469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2222 (p : Pattern) (guard : d1016 p = 1) : d109 p ≤ (0 : Int) + d470 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2197 p hg
    simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2221 p hg
    simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2223 (p : Pattern) (guard : d1016 p = 1) : d109 p ≤ (0 : Int) + d471 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2197 p hg
    simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2222 p hg
    simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2224 (p : Pattern) (guard : d1016 p = 1) : d227 p ≤ (0 : Int) + d472 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d227, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2219 p hg
    simpa only [d227, d472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d227, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2223 p hg
    simpa only [d227, d472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2225 (p : Pattern) (guard : d1016 p = 1) : d369 p ≤ (0 : Int) + d473 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d369, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2224 p hg
    simpa only [d369, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d369, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2213 p hg
    simpa only [d369, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2226 (p : Pattern) (guard : d1016 p = 1) : d229 p ≤ (0 : Int) + d474 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d229, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2217 p hg
    simpa only [d229, d474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d229, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2203 p hg
    simpa only [d229, d474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2227 (p : Pattern) (guard : d1016 p = 1) : d230 p ≤ (0 : Int) + d475 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d230, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2221 p hg
    simpa only [d230, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d230, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2205 p hg
    simpa only [d230, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2228 (p : Pattern) (guard : d1016 p = 1) : d231 p ≤ (0 : Int) + d476 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d231, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2226 p hg
    simpa only [d231, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d231, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2227 p hg
    simpa only [d231, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2229 (p : Pattern) (guard : d1016 p = 1) : d370 p ≤ (0 : Int) + d477 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d370, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2228 p hg
    simpa only [d370, d477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d370, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2213 p hg
    simpa only [d370, d477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2230 (p : Pattern) (guard : d1016 p = 1) : d371 p ≤ (0 : Int) + d478 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d371, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2225 p hg
    simpa only [d371, d478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d371, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2229 p hg
    simpa only [d371, d478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2231 (p : Pattern) (guard : d1016 p = 1) : d229 p ≤ (0 : Int) + d479 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d229, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2218 p hg
    simpa only [d229, d479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d229, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2203 p hg
    simpa only [d229, d479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2232 (p : Pattern) (guard : d1016 p = 1) : d230 p ≤ (0 : Int) + d480 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d230, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2222 p hg
    simpa only [d230, d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d230, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2205 p hg
    simpa only [d230, d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2233 (p : Pattern) (guard : d1016 p = 1) : d231 p ≤ (0 : Int) + d481 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d231, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2231 p hg
    simpa only [d231, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d231, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2232 p hg
    simpa only [d231, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2234 (p : Pattern) (guard : d1016 p = 1) : d370 p ≤ (0 : Int) + d482 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d370, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2233 p hg
    simpa only [d370, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d370, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2213 p hg
    simpa only [d370, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2235 (p : Pattern) (guard : d1016 p = 1) : d372 p ≤ (0 : Int) + d483 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d372, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2234 p hg
    simpa only [d372, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d372, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2213 p hg
    simpa only [d372, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2236 (p : Pattern) (guard : d1016 p = 1) : d373 p ≤ (0 : Int) + d484 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d373, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2230 p hg
    simpa only [d373, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d373, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2235 p hg
    simpa only [d373, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2237 (p : Pattern) (guard : d1016 p = 1) : d374 p ≤ (0 : Int) + d485 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1016 p = 1 := by simpa only [d374, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2215 p hg
    simpa only [d374, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d374, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2236 p hg
    simpa only [d374, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2238 (p : Pattern) (guard : d828 p = 1) : d7 p ≤ (2 : Int) + d7 p := by
  omega
theorem compare2239 (p : Pattern) (guard : d1017 p = 1) : d106 p ≤ (2 : Int) + d7 p := by
  cases selected : p 160 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d1017, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2238 p hg
    simpa only [d1017, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1017, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare767 p hg
    simpa only [d1017, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
