/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons289
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare40600 (p : Pattern) (guard : d8106 p = 1) : d2198 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2198, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40599 p hg
    simpa only [d8106, d2198, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2198, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40236 p hg
    simpa only [d8106, d2198, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40601 (p : Pattern) (guard : d8112 p = 1) : d2234 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2234, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40600 p hg
    simpa only [d8112, d2234, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2234, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40260 p hg
    simpa only [d8112, d2234, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40602 (p : Pattern) (guard : d8113 p = 1) : d2264 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2264, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40597 p hg
    simpa only [d8113, d2264, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2264, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40601 p hg
    simpa only [d8113, d2264, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40603 (p : Pattern) (guard : d8112 p = 1) : d2239 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2239, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40437 p hg
    simpa only [d8112, d2239, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2239, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40264 p hg
    simpa only [d8112, d2239, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40604 (p : Pattern) (guard : d8118 p = 1) : d2242 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2242, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40603 p hg
    simpa only [d8118, d2242, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2242, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40268 p hg
    simpa only [d8118, d2242, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40605 (p : Pattern) (guard : d8119 p = 1) : d2265 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2265, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40602 p hg
    simpa only [d8119, d2265, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2265, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40604 p hg
    simpa only [d8119, d2265, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40606 (p : Pattern) (guard : d8106 p = 1) : d2214 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2214, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40476 p hg
    simpa only [d8106, d2214, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2214, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40247 p hg
    simpa only [d8106, d2214, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40607 (p : Pattern) (guard : d8112 p = 1) : d2245 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2245, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40606 p hg
    simpa only [d8112, d2245, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2245, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40445 p hg
    simpa only [d8112, d2245, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40608 (p : Pattern) (guard : d8118 p = 1) : d2247 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2247, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40607 p hg
    simpa only [d8118, d2247, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2247, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40448 p hg
    simpa only [d8118, d2247, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40609 (p : Pattern) (guard : d8124 p = 1) : d2253 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2253, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40608 p hg
    simpa only [d8124, d2253, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2253, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40453 p hg
    simpa only [d8124, d2253, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40610 (p : Pattern) (guard : d8125 p = 1) : d2291 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2291, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40605 p hg
    simpa only [d8125, d2291, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2291, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40609 p hg
    simpa only [d8125, d2291, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40611 (p : Pattern) (guard : d8126 p = 1) : d2292 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2292, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40590 p hg
    simpa only [d8126, d2292, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2292, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40610 p hg
    simpa only [d8126, d2292, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40612 (p : Pattern) (guard : d8132 p = 1) : d2293 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2293, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40611 p hg
    simpa only [d8132, d2293, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2293, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40506 p hg
    simpa only [d8132, d2293, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40613 (p : Pattern) (guard : d8107 p = 1) : d2201 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40383 p hg
    simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40501 p hg
    simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40614 (p : Pattern) (guard : d8112 p = 1) : d2202 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2202, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40477 p hg
    simpa only [d8112, d2202, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2202, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40461 p hg
    simpa only [d8112, d2202, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40615 (p : Pattern) (guard : d8113 p = 1) : d2256 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2256, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40613 p hg
    simpa only [d8113, d2256, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2256, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40614 p hg
    simpa only [d8113, d2256, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40616 (p : Pattern) (guard : d8119 p = 1) : d2257 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2257, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40615 p hg
    simpa only [d8119, d2257, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2257, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40465 p hg
    simpa only [d8119, d2257, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40617 (p : Pattern) (guard : d8125 p = 1) : d2262 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2262, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40616 p hg
    simpa only [d8125, d2262, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2262, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40473 p hg
    simpa only [d8125, d2262, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40618 (p : Pattern) (guard : d8094 p = 1) : d2185 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2185, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35445 p hg
    simpa only [d8094, d2185, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2185, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2185, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40619 (p : Pattern) (guard : d8100 p = 1) : d2185 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40618 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40412 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40620 (p : Pattern) (guard : d8106 p = 1) : d2201 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2201, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40619 p hg
    simpa only [d8106, d2201, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2201, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40457 p hg
    simpa only [d8106, d2201, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40621 (p : Pattern) (guard : d8112 p = 1) : d2263 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2263, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40620 p hg
    simpa only [d8112, d2263, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2263, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40479 p hg
    simpa only [d8112, d2263, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40622 (p : Pattern) (guard : d8118 p = 1) : d2264 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2264, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40621 p hg
    simpa only [d8118, d2264, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2264, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40482 p hg
    simpa only [d8118, d2264, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40623 (p : Pattern) (guard : d8124 p = 1) : d2265 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2265, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40622 p hg
    simpa only [d8124, d2265, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2265, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40487 p hg
    simpa only [d8124, d2265, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40624 (p : Pattern) (guard : d8130 p = 1) : d2269 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2269, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40623 p hg
    simpa only [d8130, d2269, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2269, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40491 p hg
    simpa only [d8130, d2269, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40625 (p : Pattern) (guard : d8131 p = 1) : d2270 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2270, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40617 p hg
    simpa only [d8131, d2270, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2270, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40624 p hg
    simpa only [d8131, d2270, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40626 (p : Pattern) (guard : d8137 p = 1) : d2294 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2294, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40625 p hg
    simpa only [d8137, d2294, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2294, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d2294, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40627 (p : Pattern) (guard : d8138 p = 1) : d2295 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d2295, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40612 p hg
    simpa only [d8138, d2295, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d2295, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40626 p hg
    simpa only [d8138, d2295, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40628 (p : Pattern) (guard : d8139 p = 1) : d2296 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d2296, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40580 p hg
    simpa only [d8139, d2296, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d2296, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40627 p hg
    simpa only [d8139, d2296, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40629 (p : Pattern) (guard : d8085 p = 1) : d320 p ≤ (0 : Int) + d320 p := by
  omega
theorem compare40630 (p : Pattern) (guard : d8086 p = 1) : d2318 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d2318, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35089 p hg
    simpa only [d8086, d2318, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d2318, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40629 p hg
    simpa only [d8086, d2318, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40631 (p : Pattern) (guard : d8090 p = 1) : d2319 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2319, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35097 p hg
    simpa only [d8090, d2319, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2319, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2319, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40632 (p : Pattern) (guard : d8091 p = 1) : d2320 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2320, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40630 p hg
    simpa only [d8091, d2320, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2320, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40631 p hg
    simpa only [d8091, d2320, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40633 (p : Pattern) (guard : d8090 p = 1) : d2319 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2319, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35095 p hg
    simpa only [d8090, d2319, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2319, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2319, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40634 (p : Pattern) (guard : d8095 p = 1) : d2321 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2321, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40633 p hg
    simpa only [d8095, d2321, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2321, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d2321, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40635 (p : Pattern) (guard : d8096 p = 1) : d2322 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2322, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40632 p hg
    simpa only [d8096, d2322, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2322, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40634 p hg
    simpa only [d8096, d2322, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40636 (p : Pattern) (guard : d8089 p = 1) : d332 p ≤ (0 : Int) + d332 p := by
  omega
theorem compare40637 (p : Pattern) (guard : d8090 p = 1) : d2323 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2323, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35109 p hg
    simpa only [d8090, d2323, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2323, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40636 p hg
    simpa only [d8090, d2323, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40638 (p : Pattern) (guard : d8094 p = 1) : d2319 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35100 p hg
    simpa only [d8094, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40639 (p : Pattern) (guard : d8095 p = 1) : d2324 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2324, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40637 p hg
    simpa only [d8095, d2324, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2324, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40638 p hg
    simpa only [d8095, d2324, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40640 (p : Pattern) (guard : d8094 p = 1) : d2319 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2319, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35112 p hg
    simpa only [d8094, d2319, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2319, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2319, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40641 (p : Pattern) (guard : d8100 p = 1) : d2321 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2321, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40640 p hg
    simpa only [d8100, d2321, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2321, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2321, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40642 (p : Pattern) (guard : d8101 p = 1) : d2325 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2325, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40639 p hg
    simpa only [d8101, d2325, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2325, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40641 p hg
    simpa only [d8101, d2325, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40643 (p : Pattern) (guard : d8102 p = 1) : d2326 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2326, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40635 p hg
    simpa only [d8102, d2326, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2326, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40642 p hg
    simpa only [d8102, d2326, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40644 (p : Pattern) (guard : d8090 p = 1) : d2319 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2319, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35123 p hg
    simpa only [d8090, d2319, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2319, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2319, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40645 (p : Pattern) (guard : d8095 p = 1) : d2319 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40644 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40638 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40646 (p : Pattern) (guard : d8100 p = 1) : d2321 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40638 p hg
    simpa only [d8100, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40647 (p : Pattern) (guard : d8101 p = 1) : d2327 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2327, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40645 p hg
    simpa only [d8101, d2327, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2327, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40646 p hg
    simpa only [d8101, d2327, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40648 (p : Pattern) (guard : d8094 p = 1) : d2328 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2328, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35134 p hg
    simpa only [d8094, d2328, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2328, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2328, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40649 (p : Pattern) (guard : d8099 p = 1) : d2328 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35135 p hg
    simpa only [d8099, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40650 (p : Pattern) (guard : d8100 p = 1) : d2328 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40648 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40649 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40651 (p : Pattern) (guard : d8105 p = 1) : d2329 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40649 p hg
    simpa only [d8105, d2329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40652 (p : Pattern) (guard : d8106 p = 1) : d2330 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2330, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40650 p hg
    simpa only [d8106, d2330, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2330, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40651 p hg
    simpa only [d8106, d2330, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40653 (p : Pattern) (guard : d8107 p = 1) : d2331 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2331, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40647 p hg
    simpa only [d8107, d2331, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2331, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40652 p hg
    simpa only [d8107, d2331, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40654 (p : Pattern) (guard : d8108 p = 1) : d2332 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2332, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40643 p hg
    simpa only [d8108, d2332, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2332, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40653 p hg
    simpa only [d8108, d2332, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40655 (p : Pattern) (guard : d8090 p = 1) : d2319 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2319, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35146 p hg
    simpa only [d8090, d2319, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2319, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2319, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40656 (p : Pattern) (guard : d8095 p = 1) : d2319 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40655 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40638 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40657 (p : Pattern) (guard : d8101 p = 1) : d2327 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2327, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40656 p hg
    simpa only [d8101, d2327, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2327, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40646 p hg
    simpa only [d8101, d2327, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40658 (p : Pattern) (guard : d8094 p = 1) : d2328 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2328, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35152 p hg
    simpa only [d8094, d2328, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2328, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2328, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40659 (p : Pattern) (guard : d8100 p = 1) : d2328 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40658 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40649 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40660 (p : Pattern) (guard : d8106 p = 1) : d2330 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2330, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40659 p hg
    simpa only [d8106, d2330, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2330, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40651 p hg
    simpa only [d8106, d2330, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40661 (p : Pattern) (guard : d8107 p = 1) : d2331 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2331, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40657 p hg
    simpa only [d8107, d2331, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2331, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40660 p hg
    simpa only [d8107, d2331, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40662 (p : Pattern) (guard : d8112 p = 1) : d2333 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2333, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40549 p hg
    simpa only [d8112, d2333, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2333, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2333, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40663 (p : Pattern) (guard : d8113 p = 1) : d2334 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2334, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40661 p hg
    simpa only [d8113, d2334, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2334, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40662 p hg
    simpa only [d8113, d2334, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40664 (p : Pattern) (guard : d8114 p = 1) : d2335 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2335, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40654 p hg
    simpa only [d8114, d2335, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2335, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40663 p hg
    simpa only [d8114, d2335, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40665 (p : Pattern) (guard : d8090 p = 1) : d2319 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2319, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35162 p hg
    simpa only [d8090, d2319, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2319, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39959 p hg
    simpa only [d8090, d2319, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40666 (p : Pattern) (guard : d8095 p = 1) : d2319 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40665 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40638 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40667 (p : Pattern) (guard : d8094 p = 1) : d2336 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35169 p hg
    simpa only [d8094, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40668 (p : Pattern) (guard : d8100 p = 1) : d2337 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40667 p hg
    simpa only [d8100, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40669 (p : Pattern) (guard : d8101 p = 1) : d2338 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2338, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40666 p hg
    simpa only [d8101, d2338, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2338, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40668 p hg
    simpa only [d8101, d2338, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40670 (p : Pattern) (guard : d8094 p = 1) : d2319 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2319, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35176 p hg
    simpa only [d8094, d2319, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2319, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2319, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40671 (p : Pattern) (guard : d8099 p = 1) : d2319 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35114 p hg
    simpa only [d8099, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40672 (p : Pattern) (guard : d8100 p = 1) : d2319 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40670 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40671 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40673 (p : Pattern) (guard : d8099 p = 1) : d2339 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35182 p hg
    simpa only [d8099, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40674 (p : Pattern) (guard : d8105 p = 1) : d2340 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40673 p hg
    simpa only [d8105, d2340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40675 (p : Pattern) (guard : d8106 p = 1) : d2341 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2341, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40672 p hg
    simpa only [d8106, d2341, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2341, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40674 p hg
    simpa only [d8106, d2341, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40676 (p : Pattern) (guard : d8107 p = 1) : d2342 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2342, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40669 p hg
    simpa only [d8107, d2342, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2342, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40675 p hg
    simpa only [d8107, d2342, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40677 (p : Pattern) (guard : d8100 p = 1) : d2319 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40640 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40671 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40678 (p : Pattern) (guard : d8106 p = 1) : d2343 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2343, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40677 p hg
    simpa only [d8106, d2343, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2343, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2343, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40679 (p : Pattern) (guard : d0 p = 1) : d2328 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40680 (p : Pattern) (guard : d8105 p = 1) : d2328 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40649 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40679 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40681 (p : Pattern) (guard : d8111 p = 1) : d2344 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40680 p hg
    simpa only [d8111, d2344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40682 (p : Pattern) (guard : d8112 p = 1) : d2345 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2345, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40678 p hg
    simpa only [d8112, d2345, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2345, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40681 p hg
    simpa only [d8112, d2345, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40683 (p : Pattern) (guard : d8113 p = 1) : d2346 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2346, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40676 p hg
    simpa only [d8113, d2346, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2346, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d8113, d2346, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40684 (p : Pattern) (guard : d8100 p = 1) : d2319 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40638 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40671 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40685 (p : Pattern) (guard : d8106 p = 1) : d2343 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40684 p hg
    simpa only [d8106, d2343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d2343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40686 (p : Pattern) (guard : d8112 p = 1) : d2345 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40685 p hg
    simpa only [d8112, d2345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40681 p hg
    simpa only [d8112, d2345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40687 (p : Pattern) (guard : d8117 p = 1) : d2347 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40222 p hg
    simpa only [d8117, d2347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40688 (p : Pattern) (guard : d8118 p = 1) : d2348 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40686 p hg
    simpa only [d8118, d2348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40687 p hg
    simpa only [d8118, d2348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40689 (p : Pattern) (guard : d8119 p = 1) : d2349 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2349, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40683 p hg
    simpa only [d8119, d2349, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2349, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40688 p hg
    simpa only [d8119, d2349, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40690 (p : Pattern) (guard : d8120 p = 1) : d2350 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2350, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40664 p hg
    simpa only [d8120, d2350, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2350, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40689 p hg
    simpa only [d8120, d2350, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40691 (p : Pattern) (guard : d8089 p = 1) : d330 p ≤ (0 : Int) + d330 p := by
  omega
theorem compare40692 (p : Pattern) (guard : d8090 p = 1) : d2351 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2351, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35202 p hg
    simpa only [d8090, d2351, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2351, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40691 p hg
    simpa only [d8090, d2351, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40693 (p : Pattern) (guard : d8095 p = 1) : d2352 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2352, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40692 p hg
    simpa only [d8095, d2352, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2352, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40640 p hg
    simpa only [d8095, d2352, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40694 (p : Pattern) (guard : d8100 p = 1) : d2321 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2321, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40670 p hg
    simpa only [d8100, d2321, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2321, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d2321, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40695 (p : Pattern) (guard : d8101 p = 1) : d2353 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2353, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40693 p hg
    simpa only [d8101, d2353, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2353, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40694 p hg
    simpa only [d8101, d2353, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40696 (p : Pattern) (guard : d8094 p = 1) : d2336 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2336, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35210 p hg
    simpa only [d8094, d2336, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2336, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2336, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40697 (p : Pattern) (guard : d8099 p = 1) : d2336 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35170 p hg
    simpa only [d8099, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40698 (p : Pattern) (guard : d8100 p = 1) : d2336 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40696 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40697 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40699 (p : Pattern) (guard : d8105 p = 1) : d2337 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40697 p hg
    simpa only [d8105, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40700 (p : Pattern) (guard : d8106 p = 1) : d2354 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2354, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40698 p hg
    simpa only [d8106, d2354, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2354, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40699 p hg
    simpa only [d8106, d2354, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40701 (p : Pattern) (guard : d8107 p = 1) : d2355 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2355, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40695 p hg
    simpa only [d8107, d2355, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2355, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40700 p hg
    simpa only [d8107, d2355, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40702 (p : Pattern) (guard : d8094 p = 1) : d2328 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2328, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35219 p hg
    simpa only [d8094, d2328, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2328, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2328, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40703 (p : Pattern) (guard : d8100 p = 1) : d2328 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40702 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40649 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40704 (p : Pattern) (guard : d8106 p = 1) : d2330 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2330, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40703 p hg
    simpa only [d8106, d2330, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2330, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40651 p hg
    simpa only [d8106, d2330, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40705 (p : Pattern) (guard : d8099 p = 1) : d2236 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2236, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35223 p hg
    simpa only [d8099, d2236, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2236, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2236, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40706 (p : Pattern) (guard : d8105 p = 1) : d2236 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40705 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40220 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40707 (p : Pattern) (guard : d8111 p = 1) : d2238 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2238, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40706 p hg
    simpa only [d8111, d2238, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2238, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40263 p hg
    simpa only [d8111, d2238, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40708 (p : Pattern) (guard : d8112 p = 1) : d2356 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2356, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40704 p hg
    simpa only [d8112, d2356, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2356, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40707 p hg
    simpa only [d8112, d2356, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40709 (p : Pattern) (guard : d8113 p = 1) : d2357 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2357, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40701 p hg
    simpa only [d8113, d2357, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2357, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40708 p hg
    simpa only [d8113, d2357, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40710 (p : Pattern) (guard : d8099 p = 1) : d2216 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2216, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35229 p hg
    simpa only [d8099, d2216, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2216, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2216, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40711 (p : Pattern) (guard : d8105 p = 1) : d2216 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40710 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40224 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40712 (p : Pattern) (guard : d8111 p = 1) : d2240 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2240, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40711 p hg
    simpa only [d8111, d2240, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2240, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40266 p hg
    simpa only [d8111, d2240, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40713 (p : Pattern) (guard : d8112 p = 1) : d2358 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2358, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40652 p hg
    simpa only [d8112, d2358, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2358, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40712 p hg
    simpa only [d8112, d2358, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40714 (p : Pattern) (guard : d8118 p = 1) : d2359 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2359, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40713 p hg
    simpa only [d8118, d2359, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2359, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d2359, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40715 (p : Pattern) (guard : d8119 p = 1) : d2360 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2360, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40709 p hg
    simpa only [d8119, d2360, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2360, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40714 p hg
    simpa only [d8119, d2360, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40716 (p : Pattern) (guard : d8094 p = 1) : d2319 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2319, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35237 p hg
    simpa only [d8094, d2319, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2319, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2319, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40717 (p : Pattern) (guard : d8100 p = 1) : d2319 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40716 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40671 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40718 (p : Pattern) (guard : d8106 p = 1) : d2341 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2341, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40717 p hg
    simpa only [d8106, d2341, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2341, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40674 p hg
    simpa only [d8106, d2341, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40719 (p : Pattern) (guard : d0 p = 1) : d2336 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40720 (p : Pattern) (guard : d8105 p = 1) : d2336 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40697 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40719 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40721 (p : Pattern) (guard : d8111 p = 1) : d2361 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40720 p hg
    simpa only [d8111, d2361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40722 (p : Pattern) (guard : d8112 p = 1) : d2362 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2362, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40718 p hg
    simpa only [d8112, d2362, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2362, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40721 p hg
    simpa only [d8112, d2362, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40723 (p : Pattern) (guard : d8117 p = 1) : d2363 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40681 p hg
    simpa only [d8117, d2363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40450 p hg
    simpa only [d8117, d2363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40724 (p : Pattern) (guard : d8118 p = 1) : d2364 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2364, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40722 p hg
    simpa only [d8118, d2364, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2364, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40723 p hg
    simpa only [d8118, d2364, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40725 (p : Pattern) (guard : d0 p = 1) : d2250 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40726 (p : Pattern) (guard : d8117 p = 1) : d2365 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40681 p hg
    simpa only [d8117, d2365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40725 p hg
    simpa only [d8117, d2365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40727 (p : Pattern) (guard : d8123 p = 1) : d2366 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40726 p hg
    simpa only [d8123, d2366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40728 (p : Pattern) (guard : d8124 p = 1) : d2367 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2367, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40724 p hg
    simpa only [d8124, d2367, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2367, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40727 p hg
    simpa only [d8124, d2367, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40729 (p : Pattern) (guard : d8125 p = 1) : d2368 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2368, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40715 p hg
    simpa only [d8125, d2368, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2368, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40728 p hg
    simpa only [d8125, d2368, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40730 (p : Pattern) (guard : d8126 p = 1) : d2369 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2369, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40690 p hg
    simpa only [d8126, d2369, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2369, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40729 p hg
    simpa only [d8126, d2369, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40731 (p : Pattern) (guard : d8105 p = 1) : d2321 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40671 p hg
    simpa only [d8105, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40732 (p : Pattern) (guard : d8106 p = 1) : d2327 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2327, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40717 p hg
    simpa only [d8106, d2327, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2327, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40731 p hg
    simpa only [d8106, d2327, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40733 (p : Pattern) (guard : d8107 p = 1) : d2327 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40657 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40732 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40734 (p : Pattern) (guard : d8106 p = 1) : d2327 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2327, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40672 p hg
    simpa only [d8106, d2327, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2327, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40731 p hg
    simpa only [d8106, d2327, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40735 (p : Pattern) (guard : d0 p = 1) : d2329 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40736 (p : Pattern) (guard : d8111 p = 1) : d2330 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40680 p hg
    simpa only [d8111, d2330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40735 p hg
    simpa only [d8111, d2330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40737 (p : Pattern) (guard : d8112 p = 1) : d2331 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2331, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40734 p hg
    simpa only [d8112, d2331, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2331, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40736 p hg
    simpa only [d8112, d2331, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40738 (p : Pattern) (guard : d8113 p = 1) : d2370 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2370, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40733 p hg
    simpa only [d8113, d2370, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2370, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40737 p hg
    simpa only [d8113, d2370, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40739 (p : Pattern) (guard : d8106 p = 1) : d2327 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2327, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40677 p hg
    simpa only [d8106, d2327, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2327, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40731 p hg
    simpa only [d8106, d2327, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
