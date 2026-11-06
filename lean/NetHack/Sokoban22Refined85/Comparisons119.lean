/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons118
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare16660 (p : Pattern) (guard : d4474 p = 1) : d2092 p ≤ (0 : Int) + d3145 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2092, d3145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16505 p hg
    simpa only [d2092, d3145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2092, d3145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2092, d3145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16661 (p : Pattern) (guard : d4474 p = 1) : d2093 p ≤ (0 : Int) + d3146 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2093, d3146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16526 p hg
    simpa only [d2093, d3146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2093, d3146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16660 p hg
    simpa only [d2093, d3146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16662 (p : Pattern) (guard : d4474 p = 1) : d2094 p ≤ (0 : Int) + d3147 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2094, d3147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16660 p hg
    simpa only [d2094, d3147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2094, d3147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2094, d3147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16663 (p : Pattern) (guard : d4474 p = 1) : d2095 p ≤ (0 : Int) + d3148 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2095, d3148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16661 p hg
    simpa only [d2095, d3148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2095, d3148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16662 p hg
    simpa only [d2095, d3148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16664 (p : Pattern) (guard : d4474 p = 1) : d2096 p ≤ (0 : Int) + d3149 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2096, d3149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16659 p hg
    simpa only [d2096, d3149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2096, d3149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16663 p hg
    simpa only [d2096, d3149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16665 (p : Pattern) (guard : d4474 p = 1) : d2097 p ≤ (0 : Int) + d3150 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2097, d3150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16511 p hg
    simpa only [d2097, d3150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2097, d3150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16664 p hg
    simpa only [d2097, d3150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16666 (p : Pattern) (guard : d4474 p = 1) : d2098 p ≤ (0 : Int) + d3151 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2098, d3151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16545 p hg
    simpa only [d2098, d3151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2098, d3151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2098, d3151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16667 (p : Pattern) (guard : d4474 p = 1) : d2099 p ≤ (0 : Int) + d3152 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2099, d3152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16557 p hg
    simpa only [d2099, d3152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2099, d3152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16666 p hg
    simpa only [d2099, d3152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16668 (p : Pattern) (guard : d4474 p = 1) : d2100 p ≤ (0 : Int) + d3153 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2100, d3153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16666 p hg
    simpa only [d2100, d3153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2100, d3153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2100, d3153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16669 (p : Pattern) (guard : d4474 p = 1) : d2101 p ≤ (0 : Int) + d3154 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2101, d3154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16667 p hg
    simpa only [d2101, d3154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2101, d3154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16668 p hg
    simpa only [d2101, d3154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16670 (p : Pattern) (guard : d4474 p = 1) : d2102 p ≤ (0 : Int) + d3155 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2102, d3155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16669 p hg
    simpa only [d2102, d3155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2102, d3155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16565 p hg
    simpa only [d2102, d3155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16671 (p : Pattern) (guard : d4474 p = 1) : d2103 p ≤ (0 : Int) + d3156 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2103, d3156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d2103, d3156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2103, d3156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16670 p hg
    simpa only [d2103, d3156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16672 (p : Pattern) (guard : d4474 p = 1) : d2104 p ≤ (0 : Int) + d3157 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2104, d3157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16665 p hg
    simpa only [d2104, d3157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2104, d3157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16671 p hg
    simpa only [d2104, d3157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16673 (p : Pattern) (guard : d4474 p = 1) : d2105 p ≤ (0 : Int) + d3158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2105, d3158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16671 p hg
    simpa only [d2105, d3158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2105, d3158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16572 p hg
    simpa only [d2105, d3158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16674 (p : Pattern) (guard : d4474 p = 1) : d2106 p ≤ (0 : Int) + d3159 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2106, d3159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16672 p hg
    simpa only [d2106, d3159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2106, d3159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16673 p hg
    simpa only [d2106, d3159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16675 (p : Pattern) (guard : d4474 p = 1) : d104 p ≤ (0 : Int) + d3160 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d104, d3160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d104, d3160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d104, d3160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12905 p hg
    simpa only [d4474, d104, d3160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16676 (p : Pattern) (guard : d4474 p = 1) : d2109 p ≤ (0 : Int) + d2109 p := by
  omega
theorem compare16677 (p : Pattern) (guard : d4474 p = 1) : d2110 p ≤ (0 : Int) + d3161 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2110, d3161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16675 p hg
    simpa only [d2110, d3161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2110, d3161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16676 p hg
    simpa only [d2110, d3161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16678 (p : Pattern) (guard : d4474 p = 1) : d2111 p ≤ (0 : Int) + d3162 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2111, d3162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16677 p hg
    simpa only [d2111, d3162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2111, d3162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16545 p hg
    simpa only [d2111, d3162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16679 (p : Pattern) (guard : d4474 p = 1) : d2112 p ≤ (0 : Int) + d3163 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2112, d3163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16536 p hg
    simpa only [d2112, d3163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2112, d3163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16678 p hg
    simpa only [d2112, d3163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16680 (p : Pattern) (guard : d4474 p = 1) : d2113 p ≤ (0 : Int) + d3164 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2113, d3164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16540 p hg
    simpa only [d2113, d3164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2113, d3164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16545 p hg
    simpa only [d2113, d3164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16681 (p : Pattern) (guard : d4474 p = 1) : d2114 p ≤ (0 : Int) + d3165 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2114, d3165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16680 p hg
    simpa only [d2114, d3165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2114, d3165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d2114, d3165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16682 (p : Pattern) (guard : d4474 p = 1) : d2115 p ≤ (0 : Int) + d3166 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2115, d3166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16679 p hg
    simpa only [d2115, d3166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2115, d3166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16681 p hg
    simpa only [d2115, d3166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16683 (p : Pattern) (guard : d4474 p = 1) : d2116 p ≤ (0 : Int) + d3167 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2116, d3167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16524 p hg
    simpa only [d2116, d3167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2116, d3167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16500 p hg
    simpa only [d2116, d3167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16684 (p : Pattern) (guard : d4474 p = 1) : d2117 p ≤ (0 : Int) + d3168 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2117, d3168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16550 p hg
    simpa only [d2117, d3168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2117, d3168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16683 p hg
    simpa only [d2117, d3168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16685 (p : Pattern) (guard : d4474 p = 1) : d2118 p ≤ (0 : Int) + d3169 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2118, d3169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16684 p hg
    simpa only [d2118, d3169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2118, d3169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16660 p hg
    simpa only [d2118, d3169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16686 (p : Pattern) (guard : d4474 p = 1) : d2119 p ≤ (0 : Int) + d3170 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2119, d3170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16551 p hg
    simpa only [d2119, d3170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2119, d3170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2119, d3170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16687 (p : Pattern) (guard : d4474 p = 1) : d2120 p ≤ (0 : Int) + d3171 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2120, d3171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16686 p hg
    simpa only [d2120, d3171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2120, d3171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2120, d3171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16688 (p : Pattern) (guard : d4474 p = 1) : d2121 p ≤ (0 : Int) + d3172 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2121, d3172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16687 p hg
    simpa only [d2121, d3172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2121, d3172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2121, d3172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16689 (p : Pattern) (guard : d4474 p = 1) : d2122 p ≤ (0 : Int) + d3173 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2122, d3173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16685 p hg
    simpa only [d2122, d3173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2122, d3173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16688 p hg
    simpa only [d2122, d3173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16690 (p : Pattern) (guard : d4474 p = 1) : d2123 p ≤ (0 : Int) + d3174 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2123, d3174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16682 p hg
    simpa only [d2123, d3174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2123, d3174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16689 p hg
    simpa only [d2123, d3174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16691 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3176 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16692 (p : Pattern) (guard : d4474 p = 1) : d117 p ≤ (0 : Int) + d3177 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d117, d3177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d4474, d117, d3177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d117, d3177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16691 p hg
    simpa only [d4474, d117, d3177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16693 (p : Pattern) (guard : d4474 p = 1) : d2126 p ≤ (0 : Int) + d2126 p := by
  omega
theorem compare16694 (p : Pattern) (guard : d4474 p = 1) : d2127 p ≤ (0 : Int) + d3178 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2127, d3178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16692 p hg
    simpa only [d2127, d3178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2127, d3178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16693 p hg
    simpa only [d2127, d3178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16695 (p : Pattern) (guard : d4474 p = 1) : d2128 p ≤ (0 : Int) + d3179 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2128, d3179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16677 p hg
    simpa only [d2128, d3179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2128, d3179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16694 p hg
    simpa only [d2128, d3179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16696 (p : Pattern) (guard : d4474 p = 1) : d108 p ≤ (0 : Int) + d3180 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d108, d3180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d4474, d108, d3180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d108, d3180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13059 p hg
    simpa only [d4474, d108, d3180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16697 (p : Pattern) (guard : d4474 p = 1) : d2131 p ≤ (0 : Int) + d2131 p := by
  omega
theorem compare16698 (p : Pattern) (guard : d4474 p = 1) : d2132 p ≤ (0 : Int) + d3181 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2132, d3181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16696 p hg
    simpa only [d2132, d3181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2132, d3181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16697 p hg
    simpa only [d2132, d3181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16699 (p : Pattern) (guard : d4474 p = 1) : d2133 p ≤ (0 : Int) + d3182 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2133, d3182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16698 p hg
    simpa only [d2133, d3182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2133, d3182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2133, d3182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16700 (p : Pattern) (guard : d4474 p = 1) : d2134 p ≤ (0 : Int) + d3183 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2134, d3183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16695 p hg
    simpa only [d2134, d3183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2134, d3183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16699 p hg
    simpa only [d2134, d3183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16701 (p : Pattern) (guard : d4474 p = 1) : d2137 p ≤ (0 : Int) + d2137 p := by
  omega
theorem compare16702 (p : Pattern) (guard : d4474 p = 1) : d2138 p ≤ (0 : Int) + d3184 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2138, d3184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16504 p hg
    simpa only [d2138, d3184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2138, d3184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16701 p hg
    simpa only [d2138, d3184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16703 (p : Pattern) (guard : d4474 p = 1) : d2139 p ≤ (0 : Int) + d3185 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2139, d3185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16702 p hg
    simpa only [d2139, d3185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2139, d3185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2139, d3185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16704 (p : Pattern) (guard : d4474 p = 1) : d2140 p ≤ (0 : Int) + d3186 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2140, d3186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16703 p hg
    simpa only [d2140, d3186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2140, d3186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2140, d3186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16705 (p : Pattern) (guard : d4474 p = 1) : d2141 p ≤ (0 : Int) + d3187 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2141, d3187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16700 p hg
    simpa only [d2141, d3187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2141, d3187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16704 p hg
    simpa only [d2141, d3187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16706 (p : Pattern) (guard : d4474 p = 1) : d2142 p ≤ (0 : Int) + d3188 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2142, d3188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16504 p hg
    simpa only [d2142, d3188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2142, d3188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16500 p hg
    simpa only [d2142, d3188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16707 (p : Pattern) (guard : d4474 p = 1) : d2143 p ≤ (0 : Int) + d3189 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2143, d3189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16706 p hg
    simpa only [d2143, d3189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2143, d3189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16505 p hg
    simpa only [d2143, d3189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16708 (p : Pattern) (guard : d4474 p = 1) : d2144 p ≤ (0 : Int) + d3190 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2144, d3190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16707 p hg
    simpa only [d2144, d3190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2144, d3190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16687 p hg
    simpa only [d2144, d3190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16709 (p : Pattern) (guard : d4474 p = 1) : d2145 p ≤ (0 : Int) + d3191 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2145, d3191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16365 p hg
    simpa only [d2145, d3191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2145, d3191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2145, d3191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16710 (p : Pattern) (guard : d4474 p = 1) : d2146 p ≤ (0 : Int) + d3192 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2146, d3192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16708 p hg
    simpa only [d2146, d3192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2146, d3192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16709 p hg
    simpa only [d2146, d3192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16711 (p : Pattern) (guard : d4474 p = 1) : d2147 p ≤ (0 : Int) + d3193 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2147, d3193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16705 p hg
    simpa only [d2147, d3193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2147, d3193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16710 p hg
    simpa only [d2147, d3193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16712 (p : Pattern) (guard : d4474 p = 1) : d2148 p ≤ (0 : Int) + d3194 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2148, d3194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16690 p hg
    simpa only [d2148, d3194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2148, d3194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16711 p hg
    simpa only [d2148, d3194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16713 (p : Pattern) (guard : d4474 p = 1) : d2149 p ≤ (0 : Int) + d3195 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2149, d3195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16540 p hg
    simpa only [d2149, d3195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2149, d3195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16543 p hg
    simpa only [d2149, d3195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16714 (p : Pattern) (guard : d4474 p = 1) : d2150 p ≤ (0 : Int) + d3196 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2150, d3196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16550 p hg
    simpa only [d2150, d3196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2150, d3196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16383 p hg
    simpa only [d2150, d3196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16715 (p : Pattern) (guard : d4474 p = 1) : d2151 p ≤ (0 : Int) + d3197 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2151, d3197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16713 p hg
    simpa only [d2151, d3197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2151, d3197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16714 p hg
    simpa only [d2151, d3197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16716 (p : Pattern) (guard : d4474 p = 1) : d2152 p ≤ (0 : Int) + d3198 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2152, d3198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16715 p hg
    simpa only [d2152, d3198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2152, d3198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d2152, d3198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16717 (p : Pattern) (guard : d4474 p = 1) : d2153 p ≤ (0 : Int) + d3199 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2153, d3199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16716 p hg
    simpa only [d2153, d3199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2153, d3199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16565 p hg
    simpa only [d2153, d3199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16718 (p : Pattern) (guard : d4474 p = 1) : d2158 p ≤ (0 : Int) + d2158 p := by
  omega
theorem compare16719 (p : Pattern) (guard : d4474 p = 1) : d2159 p ≤ (0 : Int) + d3200 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2159, d3200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16524 p hg
    simpa only [d2159, d3200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2159, d3200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16718 p hg
    simpa only [d2159, d3200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16720 (p : Pattern) (guard : d4474 p = 1) : d2160 p ≤ (0 : Int) + d3201 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2160, d3201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16719 p hg
    simpa only [d2160, d3201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2160, d3201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16550 p hg
    simpa only [d2160, d3201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16721 (p : Pattern) (guard : d4474 p = 1) : d2161 p ≤ (0 : Int) + d3202 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2161, d3202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16720 p hg
    simpa only [d2161, d3202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2161, d3202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16666 p hg
    simpa only [d2161, d3202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16722 (p : Pattern) (guard : d4474 p = 1) : d2162 p ≤ (0 : Int) + d3203 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2162, d3203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16721 p hg
    simpa only [d2162, d3203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2162, d3203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16564 p hg
    simpa only [d2162, d3203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16723 (p : Pattern) (guard : d4474 p = 1) : d2163 p ≤ (0 : Int) + d3204 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2163, d3204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16415 p hg
    simpa only [d2163, d3204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2163, d3204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2163, d3204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16724 (p : Pattern) (guard : d4474 p = 1) : d2164 p ≤ (0 : Int) + d3205 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2164, d3205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16723 p hg
    simpa only [d2164, d3205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2164, d3205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2164, d3205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16725 (p : Pattern) (guard : d4474 p = 1) : d2165 p ≤ (0 : Int) + d3206 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2165, d3206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16722 p hg
    simpa only [d2165, d3206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2165, d3206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16724 p hg
    simpa only [d2165, d3206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16726 (p : Pattern) (guard : d4474 p = 1) : d2166 p ≤ (0 : Int) + d3207 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2166, d3207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16717 p hg
    simpa only [d2166, d3207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2166, d3207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16725 p hg
    simpa only [d2166, d3207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16727 (p : Pattern) (guard : d4474 p = 1) : d2167 p ≤ (0 : Int) + d3208 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2167, d3208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16712 p hg
    simpa only [d2167, d3208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2167, d3208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16726 p hg
    simpa only [d2167, d3208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16728 (p : Pattern) (guard : d4474 p = 1) : d2168 p ≤ (0 : Int) + d3209 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2168, d3209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16550 p hg
    simpa only [d2168, d3209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2168, d3209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16414 p hg
    simpa only [d2168, d3209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16729 (p : Pattern) (guard : d4474 p = 1) : d2169 p ≤ (0 : Int) + d3210 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2169, d3210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16713 p hg
    simpa only [d2169, d3210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2169, d3210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16728 p hg
    simpa only [d2169, d3210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16730 (p : Pattern) (guard : d4474 p = 1) : d2170 p ≤ (0 : Int) + d3211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2170, d3211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16545 p hg
    simpa only [d2170, d3211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2170, d3211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16414 p hg
    simpa only [d2170, d3211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16731 (p : Pattern) (guard : d4474 p = 1) : d2171 p ≤ (0 : Int) + d3212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2171, d3212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16730 p hg
    simpa only [d2171, d3212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2171, d3212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2171, d3212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16732 (p : Pattern) (guard : d4474 p = 1) : d2172 p ≤ (0 : Int) + d3213 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2172, d3213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16729 p hg
    simpa only [d2172, d3213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2172, d3213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16731 p hg
    simpa only [d2172, d3213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16733 (p : Pattern) (guard : d4474 p = 1) : d2173 p ≤ (0 : Int) + d3214 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2173, d3214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16552 p hg
    simpa only [d2173, d3214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2173, d3214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16383 p hg
    simpa only [d2173, d3214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16734 (p : Pattern) (guard : d4474 p = 1) : d2174 p ≤ (0 : Int) + d3215 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2174, d3215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16733 p hg
    simpa only [d2174, d3215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2174, d3215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2174, d3215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16735 (p : Pattern) (guard : d4474 p = 1) : d2175 p ≤ (0 : Int) + d3216 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2175, d3216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16734 p hg
    simpa only [d2175, d3216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2175, d3216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2175, d3216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16736 (p : Pattern) (guard : d4474 p = 1) : d2176 p ≤ (0 : Int) + d3217 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2176, d3217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16732 p hg
    simpa only [d2176, d3217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2176, d3217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16735 p hg
    simpa only [d2176, d3217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16737 (p : Pattern) (guard : d4474 p = 1) : d2177 p ≤ (0 : Int) + d3218 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2177, d3218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16736 p hg
    simpa only [d2177, d3218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2177, d3218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16725 p hg
    simpa only [d2177, d3218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16738 (p : Pattern) (guard : d4474 p = 1) : d2178 p ≤ (0 : Int) + d3219 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2178, d3219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16737 p hg
    simpa only [d2178, d3219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2178, d3219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2178, d3219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16739 (p : Pattern) (guard : d4474 p = 1) : d2179 p ≤ (0 : Int) + d3220 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2179, d3220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16727 p hg
    simpa only [d2179, d3220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2179, d3220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16738 p hg
    simpa only [d2179, d3220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16740 (p : Pattern) (guard : d4474 p = 1) : d2180 p ≤ (0 : Int) + d3221 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2180, d3221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16674 p hg
    simpa only [d2180, d3221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2180, d3221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16739 p hg
    simpa only [d2180, d3221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16741 (p : Pattern) (guard : d4474 p = 1) : d2181 p ≤ (0 : Int) + d3222 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2181, d3222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16459 p hg
    simpa only [d2181, d3222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2181, d3222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16740 p hg
    simpa only [d2181, d3222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16742 (p : Pattern) (guard : d4474 p = 1) : d2182 p ≤ (0 : Int) + d3223 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2182, d3223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16655 p hg
    simpa only [d2182, d3223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2182, d3223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16741 p hg
    simpa only [d2182, d3223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16743 (p : Pattern) (guard : d4474 p = 1) : d2183 p ≤ (0 : Int) + d3224 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2183, d3224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16588 p hg
    simpa only [d2183, d3224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2183, d3224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16742 p hg
    simpa only [d2183, d3224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16744 (p : Pattern) (guard : d0 p = 1) : d1687 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16745 (p : Pattern) (guard : d4967 p = 1) : d1688 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1688, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15259 p hg
    simpa only [d4967, d1688, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1688, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16744 p hg
    simpa only [d4967, d1688, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16746 (p : Pattern) (guard : d4967 p = 1) : d1690 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1690, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15263 p hg
    simpa only [d4967, d1690, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1690, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16744 p hg
    simpa only [d4967, d1690, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16747 (p : Pattern) (guard : d4967 p = 1) : d1691 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16745 p hg
    simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16746 p hg
    simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16748 (p : Pattern) (guard : d4967 p = 1) : d1692 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1692, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d1692, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1692, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16744 p hg
    simpa only [d4967, d1692, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16749 (p : Pattern) (guard : d0 p = 1) : d1697 p ≤ (0 : Int) + d19 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16750 (p : Pattern) (guard : d4967 p = 1) : d1698 p ≤ (0 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1698, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5662 p hg
    simpa only [d4967, d1698, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1698, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16749 p hg
    simpa only [d4967, d1698, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16751 (p : Pattern) (guard : d4967 p = 1) : d1699 p ≤ (0 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1699, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16748 p hg
    simpa only [d1699, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1699, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16750 p hg
    simpa only [d1699, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16752 (p : Pattern) (guard : d4967 p = 1) : d1700 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1700, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16747 p hg
    simpa only [d1700, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1700, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16751 p hg
    simpa only [d1700, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16753 (p : Pattern) (guard : d0 p = 1) : d1705 p ≤ (0 : Int) + d25 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16754 (p : Pattern) (guard : d4967 p = 1) : d1706 p ≤ (0 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1706, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5668 p hg
    simpa only [d4967, d1706, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1706, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16753 p hg
    simpa only [d4967, d1706, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16755 (p : Pattern) (guard : d4967 p = 1) : d1707 p ≤ (0 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1707, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16754 p hg
    simpa only [d1707, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1707, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1707, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16756 (p : Pattern) (guard : d4967 p = 1) : d1708 p ≤ (0 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1708, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16751 p hg
    simpa only [d1708, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1708, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16755 p hg
    simpa only [d1708, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16757 (p : Pattern) (guard : d4967 p = 1) : d1709 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1709, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16752 p hg
    simpa only [d1709, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1709, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16756 p hg
    simpa only [d1709, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16758 (p : Pattern) (guard : d0 p = 1) : d1718 p ≤ (0 : Int) + d32 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16759 (p : Pattern) (guard : d4967 p = 1) : d1719 p ≤ (0 : Int) + d33 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1719, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d1719, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1719, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16758 p hg
    simpa only [d4967, d1719, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16760 (p : Pattern) (guard : d0 p = 1) : d1725 p ≤ (0 : Int) + d36 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16761 (p : Pattern) (guard : d4967 p = 1) : d1726 p ≤ (0 : Int) + d37 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1726, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d1726, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1726, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16760 p hg
    simpa only [d4967, d1726, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16762 (p : Pattern) (guard : d4967 p = 1) : d1727 p ≤ (0 : Int) + d38 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1727, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16759 p hg
    simpa only [d1727, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1727, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16761 p hg
    simpa only [d1727, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16763 (p : Pattern) (guard : d0 p = 1) : d1730 p ≤ (0 : Int) + d41 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16764 (p : Pattern) (guard : d4967 p = 1) : d1731 p ≤ (0 : Int) + d42 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1731, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d1731, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1731, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16763 p hg
    simpa only [d4967, d1731, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16765 (p : Pattern) (guard : d4967 p = 1) : d1733 p ≤ (0 : Int) + d44 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1733, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16764 p hg
    simpa only [d1733, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1733, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15288 p hg
    simpa only [d1733, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16766 (p : Pattern) (guard : d4967 p = 1) : d1734 p ≤ (0 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1734, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16762 p hg
    simpa only [d1734, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1734, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16765 p hg
    simpa only [d1734, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16767 (p : Pattern) (guard : d4967 p = 1) : d1738 p ≤ (0 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1738, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16766 p hg
    simpa only [d1738, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1738, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15295 p hg
    simpa only [d1738, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16768 (p : Pattern) (guard : d4967 p = 1) : d1739 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1739, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16757 p hg
    simpa only [d1739, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1739, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16767 p hg
    simpa only [d1739, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16769 (p : Pattern) (guard : d4967 p = 1) : d1741 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1741, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15299 p hg
    simpa only [d4967, d1741, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1741, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16744 p hg
    simpa only [d4967, d1741, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16770 (p : Pattern) (guard : d0 p = 1) : d1746 p ≤ (0 : Int) + d32 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16771 (p : Pattern) (guard : d4967 p = 1) : d1747 p ≤ (0 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1747, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5678 p hg
    simpa only [d4967, d1747, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1747, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16770 p hg
    simpa only [d4967, d1747, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16772 (p : Pattern) (guard : d4967 p = 1) : d1748 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1748, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16769 p hg
    simpa only [d1748, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1748, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16771 p hg
    simpa only [d1748, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16773 (p : Pattern) (guard : d4967 p = 1) : d1749 p ≤ (0 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1749, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16750 p hg
    simpa only [d1749, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1749, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16754 p hg
    simpa only [d1749, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16774 (p : Pattern) (guard : d4967 p = 1) : d1750 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1750, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16772 p hg
    simpa only [d1750, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1750, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16773 p hg
    simpa only [d1750, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16775 (p : Pattern) (guard : d0 p = 1) : d1753 p ≤ (0 : Int) + d59 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16776 (p : Pattern) (guard : d4967 p = 1) : d1754 p ≤ (0 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1754, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5685 p hg
    simpa only [d4967, d1754, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1754, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16775 p hg
    simpa only [d4967, d1754, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16777 (p : Pattern) (guard : d4967 p = 1) : d1755 p ≤ (0 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1755, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16750 p hg
    simpa only [d1755, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1755, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16776 p hg
    simpa only [d1755, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16778 (p : Pattern) (guard : d4967 p = 1) : d1756 p ≤ (0 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1756, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5690 p hg
    simpa only [d4967, d1756, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1756, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16763 p hg
    simpa only [d4967, d1756, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16779 (p : Pattern) (guard : d4967 p = 1) : d1757 p ≤ (0 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1757, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16778 p hg
    simpa only [d1757, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1757, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11471 p hg
    simpa only [d1757, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16780 (p : Pattern) (guard : d4967 p = 1) : d1758 p ≤ (0 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1758, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16777 p hg
    simpa only [d1758, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1758, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16779 p hg
    simpa only [d1758, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16781 (p : Pattern) (guard : d4967 p = 1) : d1759 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1759, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16774 p hg
    simpa only [d1759, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1759, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16780 p hg
    simpa only [d1759, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16782 (p : Pattern) (guard : d4967 p = 1) : d1761 p ≤ (0 : Int) + d67 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1761, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16761 p hg
    simpa only [d1761, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1761, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15314 p hg
    simpa only [d1761, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16783 (p : Pattern) (guard : d4967 p = 1) : d1763 p ≤ (0 : Int) + d69 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1763, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16782 p hg
    simpa only [d1763, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1763, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15316 p hg
    simpa only [d1763, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16784 (p : Pattern) (guard : d4967 p = 1) : d1766 p ≤ (0 : Int) + d75 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1766, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16783 p hg
    simpa only [d1766, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1766, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15322 p hg
    simpa only [d1766, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16785 (p : Pattern) (guard : d4967 p = 1) : d1767 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1767, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16781 p hg
    simpa only [d1767, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1767, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16784 p hg
    simpa only [d1767, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16786 (p : Pattern) (guard : d4967 p = 1) : d1768 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1768, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16768 p hg
    simpa only [d1768, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1768, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16785 p hg
    simpa only [d1768, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16787 (p : Pattern) (guard : d0 p = 1) : d1773 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16788 (p : Pattern) (guard : d4967 p = 1) : d1774 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1774, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d1774, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1774, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16787 p hg
    simpa only [d4967, d1774, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16789 (p : Pattern) (guard : d0 p = 1) : d1782 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16790 (p : Pattern) (guard : d4967 p = 1) : d1783 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1783, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d1783, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1783, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16789 p hg
    simpa only [d4967, d1783, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16791 (p : Pattern) (guard : d4967 p = 1) : d1784 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16788 p hg
    simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16790 p hg
    simpa only [d1784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16792 (p : Pattern) (guard : d0 p = 1) : d1789 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16793 (p : Pattern) (guard : d4967 p = 1) : d1790 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1790, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5658 p hg
    simpa only [d4967, d1790, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1790, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16792 p hg
    simpa only [d4967, d1790, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16794 (p : Pattern) (guard : d0 p = 1) : d1798 p ≤ (0 : Int) + d19 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16795 (p : Pattern) (guard : d4967 p = 1) : d1799 p ≤ (0 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1799, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5662 p hg
    simpa only [d4967, d1799, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1799, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16794 p hg
    simpa only [d4967, d1799, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16796 (p : Pattern) (guard : d4967 p = 1) : d1800 p ≤ (0 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1800, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16793 p hg
    simpa only [d1800, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1800, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16795 p hg
    simpa only [d1800, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16797 (p : Pattern) (guard : d4967 p = 1) : d1801 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4967 p = 1 := by simpa only [d1801, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16791 p hg
    simpa only [d1801, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4967 p = 1 := by simpa only [d1801, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16796 p hg
    simpa only [d1801, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16798 (p : Pattern) (guard : d0 p = 1) : d1804 p ≤ (0 : Int) + d25 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16799 (p : Pattern) (guard : d4967 p = 1) : d1805 p ≤ (0 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d4967, d1805, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5668 p hg
    simpa only [d4967, d1805, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4967, d1805, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16798 p hg
    simpa only [d4967, d1805, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
