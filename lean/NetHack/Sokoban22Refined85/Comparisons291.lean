/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons290
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare40740 (p : Pattern) (guard : d8112 p = 1) : d2331 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2331, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40739 p hg
    simpa only [d8112, d2331, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2331, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40736 p hg
    simpa only [d8112, d2331, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40741 (p : Pattern) (guard : d8117 p = 1) : d2333 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40264 p hg
    simpa only [d8117, d2333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40742 (p : Pattern) (guard : d8118 p = 1) : d2334 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2334, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40740 p hg
    simpa only [d8118, d2334, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2334, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40741 p hg
    simpa only [d8118, d2334, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40743 (p : Pattern) (guard : d8119 p = 1) : d2371 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2371, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40738 p hg
    simpa only [d8119, d2371, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2371, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40742 p hg
    simpa only [d8119, d2371, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40744 (p : Pattern) (guard : d8100 p = 1) : d2336 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40667 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40697 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40745 (p : Pattern) (guard : d8106 p = 1) : d2354 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40744 p hg
    simpa only [d8106, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40699 p hg
    simpa only [d8106, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40746 (p : Pattern) (guard : d0 p = 1) : d2339 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40747 (p : Pattern) (guard : d8105 p = 1) : d2339 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40673 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40746 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40748 (p : Pattern) (guard : d0 p = 1) : d2340 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40749 (p : Pattern) (guard : d8111 p = 1) : d2372 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40747 p hg
    simpa only [d8111, d2372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40748 p hg
    simpa only [d8111, d2372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40750 (p : Pattern) (guard : d8112 p = 1) : d2373 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40745 p hg
    simpa only [d8112, d2373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40749 p hg
    simpa only [d8112, d2373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40751 (p : Pattern) (guard : d8118 p = 1) : d2374 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40750 p hg
    simpa only [d8118, d2374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d2374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40752 (p : Pattern) (guard : d8124 p = 1) : d2375 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40751 p hg
    simpa only [d8124, d2375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40753 (p : Pattern) (guard : d8125 p = 1) : d2376 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2376, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40743 p hg
    simpa only [d8125, d2376, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2376, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40752 p hg
    simpa only [d8125, d2376, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40754 (p : Pattern) (guard : d8094 p = 1) : d2319 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2319, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35273 p hg
    simpa only [d8094, d2319, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2319, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2319, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40755 (p : Pattern) (guard : d8100 p = 1) : d2319 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40754 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40671 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40756 (p : Pattern) (guard : d8106 p = 1) : d2327 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2327, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40755 p hg
    simpa only [d8106, d2327, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2327, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40731 p hg
    simpa only [d8106, d2327, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40757 (p : Pattern) (guard : d8099 p = 1) : d2336 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2336, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35280 p hg
    simpa only [d8099, d2336, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2336, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2336, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40758 (p : Pattern) (guard : d8105 p = 1) : d2336 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40757 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40719 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40759 (p : Pattern) (guard : d0 p = 1) : d2337 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40760 (p : Pattern) (guard : d8111 p = 1) : d2354 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2354, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40758 p hg
    simpa only [d8111, d2354, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2354, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40759 p hg
    simpa only [d8111, d2354, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40761 (p : Pattern) (guard : d8112 p = 1) : d2377 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2377, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40756 p hg
    simpa only [d8112, d2377, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2377, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40760 p hg
    simpa only [d8112, d2377, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40762 (p : Pattern) (guard : d8117 p = 1) : d2356 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40736 p hg
    simpa only [d8117, d2356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40484 p hg
    simpa only [d8117, d2356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40763 (p : Pattern) (guard : d8118 p = 1) : d2378 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2378, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40761 p hg
    simpa only [d8118, d2378, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2378, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40762 p hg
    simpa only [d8118, d2378, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40764 (p : Pattern) (guard : d0 p = 1) : d2240 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40765 (p : Pattern) (guard : d8117 p = 1) : d2358 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40736 p hg
    simpa only [d8117, d2358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40764 p hg
    simpa only [d8117, d2358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40766 (p : Pattern) (guard : d8123 p = 1) : d2359 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40765 p hg
    simpa only [d8123, d2359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40767 (p : Pattern) (guard : d8124 p = 1) : d2379 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2379, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40763 p hg
    simpa only [d8124, d2379, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2379, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40766 p hg
    simpa only [d8124, d2379, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40768 (p : Pattern) (guard : d8117 p = 1) : d2380 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40749 p hg
    simpa only [d8117, d2380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40769 (p : Pattern) (guard : d8123 p = 1) : d2381 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40768 p hg
    simpa only [d8123, d2381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40770 (p : Pattern) (guard : d8129 p = 1) : d2382 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40769 p hg
    simpa only [d8129, d2382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40771 (p : Pattern) (guard : d8130 p = 1) : d2383 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2383, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d8130, d2383, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2383, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40770 p hg
    simpa only [d8130, d2383, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40772 (p : Pattern) (guard : d8131 p = 1) : d2384 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2384, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40753 p hg
    simpa only [d8131, d2384, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2384, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40771 p hg
    simpa only [d8131, d2384, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40773 (p : Pattern) (guard : d8132 p = 1) : d2385 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2385, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40730 p hg
    simpa only [d8132, d2385, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2385, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40772 p hg
    simpa only [d8132, d2385, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40774 (p : Pattern) (guard : d8107 p = 1) : d2327 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40647 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40756 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40775 (p : Pattern) (guard : d8112 p = 1) : d2331 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2331, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40732 p hg
    simpa only [d8112, d2331, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2331, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40736 p hg
    simpa only [d8112, d2331, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40776 (p : Pattern) (guard : d8113 p = 1) : d2370 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2370, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40774 p hg
    simpa only [d8113, d2370, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2370, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40775 p hg
    simpa only [d8113, d2370, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40777 (p : Pattern) (guard : d8118 p = 1) : d2334 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2334, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40737 p hg
    simpa only [d8118, d2334, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2334, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40741 p hg
    simpa only [d8118, d2334, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40778 (p : Pattern) (guard : d8119 p = 1) : d2371 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2371, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40776 p hg
    simpa only [d8119, d2371, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2371, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40777 p hg
    simpa only [d8119, d2371, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40779 (p : Pattern) (guard : d8094 p = 1) : d2336 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2336, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38207 p hg
    simpa only [d8094, d2336, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2336, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2336, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40780 (p : Pattern) (guard : d8100 p = 1) : d2336 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40779 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40697 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40781 (p : Pattern) (guard : d8106 p = 1) : d2354 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2354, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40780 p hg
    simpa only [d8106, d2354, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2354, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40699 p hg
    simpa only [d8106, d2354, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40782 (p : Pattern) (guard : d8112 p = 1) : d2373 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2373, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40781 p hg
    simpa only [d8112, d2373, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2373, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40749 p hg
    simpa only [d8112, d2373, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40783 (p : Pattern) (guard : d8118 p = 1) : d2374 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2374, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40782 p hg
    simpa only [d8118, d2374, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2374, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d2374, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40784 (p : Pattern) (guard : d8124 p = 1) : d2375 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2375, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40783 p hg
    simpa only [d8124, d2375, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2375, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2375, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40785 (p : Pattern) (guard : d8125 p = 1) : d2376 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2376, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40778 p hg
    simpa only [d8125, d2376, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2376, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40784 p hg
    simpa only [d8125, d2376, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40786 (p : Pattern) (guard : d8094 p = 1) : d2319 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2319, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35299 p hg
    simpa only [d8094, d2319, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2319, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2319, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40787 (p : Pattern) (guard : d8100 p = 1) : d2319 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40786 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40671 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40788 (p : Pattern) (guard : d8106 p = 1) : d2327 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2327, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40787 p hg
    simpa only [d8106, d2327, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2327, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40731 p hg
    simpa only [d8106, d2327, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40789 (p : Pattern) (guard : d8099 p = 1) : d2336 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2336, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39301 p hg
    simpa only [d8099, d2336, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2336, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2336, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40790 (p : Pattern) (guard : d8105 p = 1) : d2336 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40789 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40719 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40791 (p : Pattern) (guard : d8111 p = 1) : d2354 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2354, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40790 p hg
    simpa only [d8111, d2354, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2354, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40759 p hg
    simpa only [d8111, d2354, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40792 (p : Pattern) (guard : d8112 p = 1) : d2377 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2377, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40788 p hg
    simpa only [d8112, d2377, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2377, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40791 p hg
    simpa only [d8112, d2377, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40793 (p : Pattern) (guard : d8099 p = 1) : d2328 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2328, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35306 p hg
    simpa only [d8099, d2328, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2328, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2328, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40794 (p : Pattern) (guard : d8105 p = 1) : d2328 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40793 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40679 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40795 (p : Pattern) (guard : d8111 p = 1) : d2330 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2330, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40794 p hg
    simpa only [d8111, d2330, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2330, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40735 p hg
    simpa only [d8111, d2330, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40796 (p : Pattern) (guard : d8117 p = 1) : d2356 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2356, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40795 p hg
    simpa only [d8117, d2356, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2356, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40484 p hg
    simpa only [d8117, d2356, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40797 (p : Pattern) (guard : d8118 p = 1) : d2378 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2378, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40792 p hg
    simpa only [d8118, d2378, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2378, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40796 p hg
    simpa only [d8118, d2378, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40798 (p : Pattern) (guard : d8124 p = 1) : d2379 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2379, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40797 p hg
    simpa only [d8124, d2379, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2379, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40766 p hg
    simpa only [d8124, d2379, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40799 (p : Pattern) (guard : d8130 p = 1) : d2383 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2383, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40798 p hg
    simpa only [d8130, d2383, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2383, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40770 p hg
    simpa only [d8130, d2383, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40800 (p : Pattern) (guard : d8131 p = 1) : d2384 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2384, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40785 p hg
    simpa only [d8131, d2384, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2384, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40799 p hg
    simpa only [d8131, d2384, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40801 (p : Pattern) (guard : d8118 p = 1) : d2386 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2386, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40662 p hg
    simpa only [d8118, d2386, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2386, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d2386, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40802 (p : Pattern) (guard : d8124 p = 1) : d2387 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2387, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40801 p hg
    simpa only [d8124, d2387, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2387, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2387, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40803 (p : Pattern) (guard : d8130 p = 1) : d2388 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2388, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40802 p hg
    simpa only [d8130, d2388, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2388, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d2388, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40804 (p : Pattern) (guard : d8136 p = 1) : d2389 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2389, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40803 p hg
    simpa only [d8136, d2389, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2389, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37270 p hg
    simpa only [d8136, d2389, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40805 (p : Pattern) (guard : d8137 p = 1) : d2390 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2390, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40800 p hg
    simpa only [d8137, d2390, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2390, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40804 p hg
    simpa only [d8137, d2390, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40806 (p : Pattern) (guard : d8138 p = 1) : d2391 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d2391, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40773 p hg
    simpa only [d8138, d2391, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d2391, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40805 p hg
    simpa only [d8138, d2391, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40807 (p : Pattern) (guard : d8107 p = 1) : d2392 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2392, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40642 p hg
    simpa only [d8107, d2392, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2392, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40788 p hg
    simpa only [d8107, d2392, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40808 (p : Pattern) (guard : d8112 p = 1) : d2331 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2331, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40756 p hg
    simpa only [d8112, d2331, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2331, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40795 p hg
    simpa only [d8112, d2331, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40809 (p : Pattern) (guard : d8113 p = 1) : d2393 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2393, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40807 p hg
    simpa only [d8113, d2393, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2393, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40808 p hg
    simpa only [d8113, d2393, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40810 (p : Pattern) (guard : d8118 p = 1) : d2334 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2334, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40775 p hg
    simpa only [d8118, d2334, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2334, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40741 p hg
    simpa only [d8118, d2334, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40811 (p : Pattern) (guard : d8119 p = 1) : d2394 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2394, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40809 p hg
    simpa only [d8119, d2394, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2394, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40810 p hg
    simpa only [d8119, d2394, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40812 (p : Pattern) (guard : d8106 p = 1) : d2338 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2338, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40672 p hg
    simpa only [d8106, d2338, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2338, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40699 p hg
    simpa only [d8106, d2338, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40813 (p : Pattern) (guard : d0 p = 1) : d2319 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40814 (p : Pattern) (guard : d8105 p = 1) : d2319 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40671 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40813 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40815 (p : Pattern) (guard : d8111 p = 1) : d2341 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40814 p hg
    simpa only [d8111, d2341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40748 p hg
    simpa only [d8111, d2341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40816 (p : Pattern) (guard : d8112 p = 1) : d2342 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2342, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40812 p hg
    simpa only [d8112, d2342, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2342, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40815 p hg
    simpa only [d8112, d2342, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40817 (p : Pattern) (guard : d8111 p = 1) : d2343 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40814 p hg
    simpa only [d8111, d2343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d2343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40818 (p : Pattern) (guard : d0 p = 1) : d2344 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40819 (p : Pattern) (guard : d8117 p = 1) : d2345 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40817 p hg
    simpa only [d8117, d2345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40818 p hg
    simpa only [d8117, d2345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40820 (p : Pattern) (guard : d8118 p = 1) : d2346 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2346, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40816 p hg
    simpa only [d8118, d2346, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2346, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40819 p hg
    simpa only [d8118, d2346, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40821 (p : Pattern) (guard : d0 p = 1) : d2347 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40822 (p : Pattern) (guard : d8123 p = 1) : d2348 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40819 p hg
    simpa only [d8123, d2348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40821 p hg
    simpa only [d8123, d2348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40823 (p : Pattern) (guard : d8124 p = 1) : d2349 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2349, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40820 p hg
    simpa only [d8124, d2349, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2349, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40822 p hg
    simpa only [d8124, d2349, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40824 (p : Pattern) (guard : d8125 p = 1) : d2395 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2395, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40811 p hg
    simpa only [d8125, d2395, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2395, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40823 p hg
    simpa only [d8125, d2395, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40825 (p : Pattern) (guard : d8094 p = 1) : d2319 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2319, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35326 p hg
    simpa only [d8094, d2319, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2319, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d8094, d2319, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40826 (p : Pattern) (guard : d8100 p = 1) : d2319 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40825 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40671 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40827 (p : Pattern) (guard : d8106 p = 1) : d2327 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2327, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40826 p hg
    simpa only [d8106, d2327, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2327, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40731 p hg
    simpa only [d8106, d2327, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40828 (p : Pattern) (guard : d8099 p = 1) : d2336 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2336, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35332 p hg
    simpa only [d8099, d2336, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2336, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2336, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40829 (p : Pattern) (guard : d8105 p = 1) : d2336 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40828 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40719 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40830 (p : Pattern) (guard : d8111 p = 1) : d2354 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2354, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40829 p hg
    simpa only [d8111, d2354, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2354, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40759 p hg
    simpa only [d8111, d2354, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40831 (p : Pattern) (guard : d8112 p = 1) : d2377 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2377, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40827 p hg
    simpa only [d8112, d2377, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2377, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40830 p hg
    simpa only [d8112, d2377, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40832 (p : Pattern) (guard : d8099 p = 1) : d2328 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2328, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35339 p hg
    simpa only [d8099, d2328, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2328, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2328, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40833 (p : Pattern) (guard : d8105 p = 1) : d2328 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40832 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40679 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40834 (p : Pattern) (guard : d8111 p = 1) : d2330 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2330, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40833 p hg
    simpa only [d8111, d2330, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2330, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40735 p hg
    simpa only [d8111, d2330, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40835 (p : Pattern) (guard : d8117 p = 1) : d2356 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2356, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40834 p hg
    simpa only [d8117, d2356, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2356, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40484 p hg
    simpa only [d8117, d2356, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40836 (p : Pattern) (guard : d8118 p = 1) : d2378 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2378, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40831 p hg
    simpa only [d8118, d2378, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2378, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40835 p hg
    simpa only [d8118, d2378, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40837 (p : Pattern) (guard : d8117 p = 1) : d2358 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2358, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40795 p hg
    simpa only [d8117, d2358, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2358, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40764 p hg
    simpa only [d8117, d2358, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40838 (p : Pattern) (guard : d8123 p = 1) : d2359 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2359, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40837 p hg
    simpa only [d8123, d2359, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2359, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2359, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40839 (p : Pattern) (guard : d8124 p = 1) : d2379 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2379, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40836 p hg
    simpa only [d8124, d2379, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2379, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40838 p hg
    simpa only [d8124, d2379, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40840 (p : Pattern) (guard : d0 p = 1) : d2361 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40841 (p : Pattern) (guard : d8117 p = 1) : d2362 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40815 p hg
    simpa only [d8117, d2362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40840 p hg
    simpa only [d8117, d2362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40842 (p : Pattern) (guard : d0 p = 1) : d2363 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40843 (p : Pattern) (guard : d8123 p = 1) : d2364 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40841 p hg
    simpa only [d8123, d2364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40842 p hg
    simpa only [d8123, d2364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40844 (p : Pattern) (guard : d0 p = 1) : d2366 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40845 (p : Pattern) (guard : d8129 p = 1) : d2367 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40843 p hg
    simpa only [d8129, d2367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40844 p hg
    simpa only [d8129, d2367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40846 (p : Pattern) (guard : d8130 p = 1) : d2396 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2396, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40839 p hg
    simpa only [d8130, d2396, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2396, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40845 p hg
    simpa only [d8130, d2396, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40847 (p : Pattern) (guard : d8131 p = 1) : d2397 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2397, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40824 p hg
    simpa only [d8131, d2397, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2397, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40846 p hg
    simpa only [d8131, d2397, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40848 (p : Pattern) (guard : d0 p = 1) : d2321 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40849 (p : Pattern) (guard : d8111 p = 1) : d2327 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40814 p hg
    simpa only [d8111, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40848 p hg
    simpa only [d8111, d2327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40850 (p : Pattern) (guard : d8112 p = 1) : d2327 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40732 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40849 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40851 (p : Pattern) (guard : d0 p = 1) : d2330 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40852 (p : Pattern) (guard : d8117 p = 1) : d2331 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40849 p hg
    simpa only [d8117, d2331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40851 p hg
    simpa only [d8117, d2331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40853 (p : Pattern) (guard : d8118 p = 1) : d2370 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2370, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40850 p hg
    simpa only [d8118, d2370, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2370, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40852 p hg
    simpa only [d8118, d2370, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40854 (p : Pattern) (guard : d0 p = 1) : d2333 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40855 (p : Pattern) (guard : d8123 p = 1) : d2334 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40852 p hg
    simpa only [d8123, d2334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40854 p hg
    simpa only [d8123, d2334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40856 (p : Pattern) (guard : d8124 p = 1) : d2371 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2371, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40853 p hg
    simpa only [d8124, d2371, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2371, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40855 p hg
    simpa only [d8124, d2371, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40857 (p : Pattern) (guard : d8111 p = 1) : d2354 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40720 p hg
    simpa only [d8111, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40759 p hg
    simpa only [d8111, d2354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40858 (p : Pattern) (guard : d0 p = 1) : d2372 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40859 (p : Pattern) (guard : d8117 p = 1) : d2373 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40857 p hg
    simpa only [d8117, d2373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40858 p hg
    simpa only [d8117, d2373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40860 (p : Pattern) (guard : d8123 p = 1) : d2374 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40859 p hg
    simpa only [d8123, d2374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40861 (p : Pattern) (guard : d8129 p = 1) : d2375 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40860 p hg
    simpa only [d8129, d2375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40862 (p : Pattern) (guard : d8130 p = 1) : d2376 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2376, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40856 p hg
    simpa only [d8130, d2376, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2376, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40861 p hg
    simpa only [d8130, d2376, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40863 (p : Pattern) (guard : d8099 p = 1) : d2319 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2319, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35367 p hg
    simpa only [d8099, d2319, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2319, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8099, d2319, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40864 (p : Pattern) (guard : d8105 p = 1) : d2319 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40863 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40813 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40865 (p : Pattern) (guard : d8111 p = 1) : d2327 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2327, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40864 p hg
    simpa only [d8111, d2327, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2327, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40848 p hg
    simpa only [d8111, d2327, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40866 (p : Pattern) (guard : d0 p = 1) : d2354 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40867 (p : Pattern) (guard : d8117 p = 1) : d2377 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2377, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40865 p hg
    simpa only [d8117, d2377, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2377, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40866 p hg
    simpa only [d8117, d2377, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40868 (p : Pattern) (guard : d0 p = 1) : d2356 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40869 (p : Pattern) (guard : d8123 p = 1) : d2378 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2378, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40867 p hg
    simpa only [d8123, d2378, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2378, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40868 p hg
    simpa only [d8123, d2378, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40870 (p : Pattern) (guard : d0 p = 1) : d2359 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40871 (p : Pattern) (guard : d8129 p = 1) : d2379 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2379, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40869 p hg
    simpa only [d8129, d2379, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2379, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40870 p hg
    simpa only [d8129, d2379, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40872 (p : Pattern) (guard : d0 p = 1) : d2382 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40873 (p : Pattern) (guard : d8135 p = 1) : d2383 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2383, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40871 p hg
    simpa only [d8135, d2383, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2383, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40872 p hg
    simpa only [d8135, d2383, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40874 (p : Pattern) (guard : d8136 p = 1) : d2384 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2384, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40862 p hg
    simpa only [d8136, d2384, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2384, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40873 p hg
    simpa only [d8136, d2384, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40875 (p : Pattern) (guard : d8137 p = 1) : d2398 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2398, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40847 p hg
    simpa only [d8137, d2398, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2398, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40874 p hg
    simpa only [d8137, d2398, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40876 (p : Pattern) (guard : d8112 p = 1) : d2327 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40756 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40865 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40877 (p : Pattern) (guard : d8118 p = 1) : d2370 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2370, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40876 p hg
    simpa only [d8118, d2370, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2370, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40852 p hg
    simpa only [d8118, d2370, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40878 (p : Pattern) (guard : d8124 p = 1) : d2371 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2371, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40877 p hg
    simpa only [d8124, d2371, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2371, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40855 p hg
    simpa only [d8124, d2371, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40879 (p : Pattern) (guard : d8130 p = 1) : d2376 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2376, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40878 p hg
    simpa only [d8130, d2376, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2376, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40861 p hg
    simpa only [d8130, d2376, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
