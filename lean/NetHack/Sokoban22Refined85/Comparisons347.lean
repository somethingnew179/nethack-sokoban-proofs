/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons346
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare48580 (p : Pattern) (guard : d8119 p = 1) : d840 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d840, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35434 p hg
    simpa only [d8119, d840, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d840, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48520 p hg
    simpa only [d8119, d840, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48581 (p : Pattern) (guard : d8118 p = 1) : d799 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d799, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48076 p hg
    simpa only [d8118, d799, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d799, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48450 p hg
    simpa only [d8118, d799, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48582 (p : Pattern) (guard : d8124 p = 1) : d800 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d800, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48581 p hg
    simpa only [d8124, d800, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d800, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d800, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48583 (p : Pattern) (guard : d8125 p = 1) : d841 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d841, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48580 p hg
    simpa only [d8125, d841, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d841, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48582 p hg
    simpa only [d8125, d841, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48584 (p : Pattern) (guard : d8126 p = 1) : d842 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d842, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48579 p hg
    simpa only [d8126, d842, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d842, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48583 p hg
    simpa only [d8126, d842, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48585 (p : Pattern) (guard : d8119 p = 1) : d843 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d843, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35457 p hg
    simpa only [d8119, d843, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d843, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48447 p hg
    simpa only [d8119, d843, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48586 (p : Pattern) (guard : d8125 p = 1) : d844 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d844, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48585 p hg
    simpa only [d8125, d844, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d844, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48457 p hg
    simpa only [d8125, d844, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48587 (p : Pattern) (guard : d8124 p = 1) : d807 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d807, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35474 p hg
    simpa only [d8124, d807, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d807, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d807, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48588 (p : Pattern) (guard : d8130 p = 1) : d812 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d812, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48587 p hg
    simpa only [d8130, d812, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d812, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48461 p hg
    simpa only [d8130, d812, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48589 (p : Pattern) (guard : d8131 p = 1) : d845 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d845, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48586 p hg
    simpa only [d8131, d845, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d845, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48588 p hg
    simpa only [d8131, d845, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48590 (p : Pattern) (guard : d8132 p = 1) : d846 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d846, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48584 p hg
    simpa only [d8132, d846, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d846, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48589 p hg
    simpa only [d8132, d846, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48591 (p : Pattern) (guard : d8119 p = 1) : d803 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d803, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35617 p hg
    simpa only [d8119, d803, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d803, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48500 p hg
    simpa only [d8119, d803, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48592 (p : Pattern) (guard : d8118 p = 1) : d804 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d804, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48091 p hg
    simpa only [d8118, d804, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d804, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35545 p hg
    simpa only [d8118, d804, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48593 (p : Pattern) (guard : d8124 p = 1) : d805 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d805, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48592 p hg
    simpa only [d8124, d805, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d805, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d805, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48594 (p : Pattern) (guard : d8125 p = 1) : d806 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d806, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48591 p hg
    simpa only [d8125, d806, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d806, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48593 p hg
    simpa only [d8125, d806, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48595 (p : Pattern) (guard : d8124 p = 1) : d807 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d807, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35632 p hg
    simpa only [d8124, d807, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d807, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d807, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48596 (p : Pattern) (guard : d8130 p = 1) : d812 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d812, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48595 p hg
    simpa only [d8130, d812, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d812, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48461 p hg
    simpa only [d8130, d812, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48597 (p : Pattern) (guard : d8131 p = 1) : d813 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d813, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48594 p hg
    simpa only [d8131, d813, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d813, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48596 p hg
    simpa only [d8131, d813, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48598 (p : Pattern) (guard : d8124 p = 1) : d820 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d820, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38244 p hg
    simpa only [d8124, d820, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d820, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d820, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48599 (p : Pattern) (guard : d8130 p = 1) : d821 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d821, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48598 p hg
    simpa only [d8130, d821, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d821, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38247 p hg
    simpa only [d8130, d821, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48600 (p : Pattern) (guard : d8136 p = 1) : d822 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d822, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48599 p hg
    simpa only [d8136, d822, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d822, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41444 p hg
    simpa only [d8136, d822, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48601 (p : Pattern) (guard : d8137 p = 1) : d847 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d847, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48597 p hg
    simpa only [d8137, d847, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d847, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48600 p hg
    simpa only [d8137, d847, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48602 (p : Pattern) (guard : d8138 p = 1) : d848 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d848, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48590 p hg
    simpa only [d8138, d848, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d848, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48601 p hg
    simpa only [d8138, d848, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48603 (p : Pattern) (guard : d8119 p = 1) : d815 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d815, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35493 p hg
    simpa only [d8119, d815, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d815, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48547 p hg
    simpa only [d8119, d815, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48604 (p : Pattern) (guard : d8118 p = 1) : d791 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d791, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48106 p hg
    simpa only [d8118, d791, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d791, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35545 p hg
    simpa only [d8118, d791, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48605 (p : Pattern) (guard : d8124 p = 1) : d826 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d826, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48604 p hg
    simpa only [d8124, d826, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d826, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d826, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48606 (p : Pattern) (guard : d8125 p = 1) : d849 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d849, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48603 p hg
    simpa only [d8125, d849, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d849, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48605 p hg
    simpa only [d8125, d849, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48607 (p : Pattern) (guard : d8124 p = 1) : d817 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d817, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35528 p hg
    simpa only [d8124, d817, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d817, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48552 p hg
    simpa only [d8124, d817, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48608 (p : Pattern) (guard : d8123 p = 1) : d799 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48115 p hg
    simpa only [d8123, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6413 p hg
    simpa only [d8123, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48609 (p : Pattern) (guard : d8129 p = 1) : d800 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48608 p hg
    simpa only [d8129, d800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48610 (p : Pattern) (guard : d8130 p = 1) : d850 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d850, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48607 p hg
    simpa only [d8130, d850, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d850, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48609 p hg
    simpa only [d8130, d850, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48611 (p : Pattern) (guard : d8131 p = 1) : d851 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d851, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48606 p hg
    simpa only [d8131, d851, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d851, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48610 p hg
    simpa only [d8131, d851, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48612 (p : Pattern) (guard : d8124 p = 1) : d898 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d898, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41463 p hg
    simpa only [d8124, d898, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d898, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d898, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48613 (p : Pattern) (guard : d8123 p = 1) : d899 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d8123, d899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6596 p hg
    simpa only [d8123, d899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48614 (p : Pattern) (guard : d8129 p = 1) : d900 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48613 p hg
    simpa only [d8129, d900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48615 (p : Pattern) (guard : d8130 p = 1) : d901 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d901, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48612 p hg
    simpa only [d8130, d901, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d901, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48614 p hg
    simpa only [d8130, d901, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48616 (p : Pattern) (guard : d8129 p = 1) : d902 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d902, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41471 p hg
    simpa only [d8129, d902, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d902, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d902, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48617 (p : Pattern) (guard : d8135 p = 1) : d905 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d905, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48616 p hg
    simpa only [d8135, d905, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d905, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7075 p hg
    simpa only [d8135, d905, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48618 (p : Pattern) (guard : d8136 p = 1) : d906 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d906, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48615 p hg
    simpa only [d8136, d906, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d906, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48617 p hg
    simpa only [d8136, d906, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48619 (p : Pattern) (guard : d8137 p = 1) : d907 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d907, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48611 p hg
    simpa only [d8137, d907, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d907, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48618 p hg
    simpa only [d8137, d907, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48620 (p : Pattern) (guard : d8124 p = 1) : d898 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d898, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41476 p hg
    simpa only [d8124, d898, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d898, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d898, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48621 (p : Pattern) (guard : d8130 p = 1) : d901 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d901, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48620 p hg
    simpa only [d8130, d901, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d901, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48614 p hg
    simpa only [d8130, d901, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48622 (p : Pattern) (guard : d8129 p = 1) : d902 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d902, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41480 p hg
    simpa only [d8129, d902, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d902, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d902, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48623 (p : Pattern) (guard : d8135 p = 1) : d905 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d905, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48622 p hg
    simpa only [d8135, d905, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d905, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7075 p hg
    simpa only [d8135, d905, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48624 (p : Pattern) (guard : d8136 p = 1) : d906 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d906, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48621 p hg
    simpa only [d8136, d906, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d906, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48623 p hg
    simpa only [d8136, d906, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48625 (p : Pattern) (guard : d8142 p = 1) : d908 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d908, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48624 p hg
    simpa only [d8142, d908, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d908, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d908, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48626 (p : Pattern) (guard : d8143 p = 1) : d909 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d909, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48619 p hg
    simpa only [d8143, d909, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d909, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48625 p hg
    simpa only [d8143, d909, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48627 (p : Pattern) (guard : d8144 p = 1) : d910 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d910, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48602 p hg
    simpa only [d8144, d910, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d910, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48626 p hg
    simpa only [d8144, d910, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48628 (p : Pattern) (guard : d8145 p = 1) : d911 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d911, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48514 p hg
    simpa only [d8145, d911, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d911, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48627 p hg
    simpa only [d8145, d911, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48629 (p : Pattern) (guard : d8113 p = 1) : d362 p ≤ (0 : Int) + d362 p := by
  omega
theorem compare48630 (p : Pattern) (guard : d8114 p = 1) : d790 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d790, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35569 p hg
    simpa only [d8114, d790, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d790, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48629 p hg
    simpa only [d8114, d790, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48631 (p : Pattern) (guard : d8113 p = 1) : d791 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d791, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48147 p hg
    simpa only [d8113, d791, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d791, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38263 p hg
    simpa only [d8113, d791, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48632 (p : Pattern) (guard : d8119 p = 1) : d792 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d792, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48631 p hg
    simpa only [d8119, d792, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d792, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48447 p hg
    simpa only [d8119, d792, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48633 (p : Pattern) (guard : d8120 p = 1) : d793 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d793, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48630 p hg
    simpa only [d8120, d793, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d793, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48632 p hg
    simpa only [d8120, d793, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48634 (p : Pattern) (guard : d8118 p = 1) : d387 p ≤ (0 : Int) + d387 p := by
  omega
theorem compare48635 (p : Pattern) (guard : d8119 p = 1) : d794 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d794, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35604 p hg
    simpa only [d8119, d794, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d794, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48634 p hg
    simpa only [d8119, d794, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48636 (p : Pattern) (guard : d8118 p = 1) : d799 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d799, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48073 p hg
    simpa only [d8118, d799, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d799, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48450 p hg
    simpa only [d8118, d799, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48637 (p : Pattern) (guard : d8124 p = 1) : d800 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d800, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48636 p hg
    simpa only [d8124, d800, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d800, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d800, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48638 (p : Pattern) (guard : d8125 p = 1) : d801 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d801, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48635 p hg
    simpa only [d8125, d801, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d801, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48637 p hg
    simpa only [d8125, d801, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48639 (p : Pattern) (guard : d8126 p = 1) : d802 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d802, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48633 p hg
    simpa only [d8126, d802, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d802, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48638 p hg
    simpa only [d8126, d802, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48640 (p : Pattern) (guard : d8132 p = 1) : d814 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d814, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48639 p hg
    simpa only [d8132, d814, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d814, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48597 p hg
    simpa only [d8132, d814, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48641 (p : Pattern) (guard : d8118 p = 1) : d804 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d804, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48165 p hg
    simpa only [d8118, d804, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d804, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35545 p hg
    simpa only [d8118, d804, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48642 (p : Pattern) (guard : d8124 p = 1) : d805 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d805, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48641 p hg
    simpa only [d8124, d805, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d805, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d805, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48643 (p : Pattern) (guard : d8125 p = 1) : d816 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d816, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48603 p hg
    simpa only [d8125, d816, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d816, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48642 p hg
    simpa only [d8125, d816, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48644 (p : Pattern) (guard : d8130 p = 1) : d818 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d818, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48607 p hg
    simpa only [d8130, d818, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d818, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48461 p hg
    simpa only [d8130, d818, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48645 (p : Pattern) (guard : d8131 p = 1) : d819 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d819, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48643 p hg
    simpa only [d8131, d819, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d819, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48644 p hg
    simpa only [d8131, d819, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48646 (p : Pattern) (guard : d8124 p = 1) : d820 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d820, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38269 p hg
    simpa only [d8124, d820, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d820, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d820, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48647 (p : Pattern) (guard : d8130 p = 1) : d821 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d821, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48646 p hg
    simpa only [d8130, d821, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d821, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38247 p hg
    simpa only [d8130, d821, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48648 (p : Pattern) (guard : d8136 p = 1) : d822 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d822, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48647 p hg
    simpa only [d8136, d822, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d822, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41492 p hg
    simpa only [d8136, d822, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48649 (p : Pattern) (guard : d8137 p = 1) : d823 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d823, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48645 p hg
    simpa only [d8137, d823, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d823, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48648 p hg
    simpa only [d8137, d823, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48650 (p : Pattern) (guard : d8138 p = 1) : d824 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d824, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48640 p hg
    simpa only [d8138, d824, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d824, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48649 p hg
    simpa only [d8138, d824, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48651 (p : Pattern) (guard : d8119 p = 1) : d825 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d825, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35641 p hg
    simpa only [d8119, d825, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d825, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48520 p hg
    simpa only [d8119, d825, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48652 (p : Pattern) (guard : d8118 p = 1) : d791 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d791, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48180 p hg
    simpa only [d8118, d791, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d791, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35545 p hg
    simpa only [d8118, d791, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48653 (p : Pattern) (guard : d8124 p = 1) : d826 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d826, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48652 p hg
    simpa only [d8124, d826, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d826, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d826, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48654 (p : Pattern) (guard : d8125 p = 1) : d827 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d827, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48651 p hg
    simpa only [d8125, d827, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d827, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48653 p hg
    simpa only [d8125, d827, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48655 (p : Pattern) (guard : d8123 p = 1) : d394 p ≤ (0 : Int) + d394 p := by
  omega
theorem compare48656 (p : Pattern) (guard : d8124 p = 1) : d828 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d828, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35668 p hg
    simpa only [d8124, d828, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d828, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48655 p hg
    simpa only [d8124, d828, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48657 (p : Pattern) (guard : d8123 p = 1) : d799 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d799, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48112 p hg
    simpa only [d8123, d799, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d799, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6413 p hg
    simpa only [d8123, d799, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48658 (p : Pattern) (guard : d8129 p = 1) : d800 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d800, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48657 p hg
    simpa only [d8129, d800, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d800, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d800, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48659 (p : Pattern) (guard : d8130 p = 1) : d829 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d829, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48656 p hg
    simpa only [d8130, d829, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d829, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48658 p hg
    simpa only [d8130, d829, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48660 (p : Pattern) (guard : d8131 p = 1) : d830 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d830, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48654 p hg
    simpa only [d8131, d830, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d830, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48659 p hg
    simpa only [d8131, d830, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48661 (p : Pattern) (guard : d8124 p = 1) : d831 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d831, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35679 p hg
    simpa only [d8124, d831, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d831, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d831, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48662 (p : Pattern) (guard : d8123 p = 1) : d804 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d8123, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6422 p hg
    simpa only [d8123, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48663 (p : Pattern) (guard : d8129 p = 1) : d805 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48662 p hg
    simpa only [d8129, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48664 (p : Pattern) (guard : d8130 p = 1) : d832 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d832, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48661 p hg
    simpa only [d8130, d832, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d832, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48663 p hg
    simpa only [d8130, d832, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48665 (p : Pattern) (guard : d8129 p = 1) : d807 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d807, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35688 p hg
    simpa only [d8129, d807, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d807, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d807, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48666 (p : Pattern) (guard : d8135 p = 1) : d812 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d812, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48665 p hg
    simpa only [d8135, d812, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d812, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6964 p hg
    simpa only [d8135, d812, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48667 (p : Pattern) (guard : d8136 p = 1) : d833 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d833, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48664 p hg
    simpa only [d8136, d833, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d833, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48666 p hg
    simpa only [d8136, d833, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48668 (p : Pattern) (guard : d8137 p = 1) : d834 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d834, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48660 p hg
    simpa only [d8137, d834, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d834, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48667 p hg
    simpa only [d8137, d834, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48669 (p : Pattern) (guard : d8124 p = 1) : d831 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d831, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38279 p hg
    simpa only [d8124, d831, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d831, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d831, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48670 (p : Pattern) (guard : d8130 p = 1) : d832 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d832, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48669 p hg
    simpa only [d8130, d832, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d832, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48663 p hg
    simpa only [d8130, d832, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48671 (p : Pattern) (guard : d8129 p = 1) : d807 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d807, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41499 p hg
    simpa only [d8129, d807, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d807, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d807, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48672 (p : Pattern) (guard : d8135 p = 1) : d812 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d812, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48671 p hg
    simpa only [d8135, d812, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d812, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6964 p hg
    simpa only [d8135, d812, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48673 (p : Pattern) (guard : d8136 p = 1) : d833 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d833, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48670 p hg
    simpa only [d8136, d833, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d833, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48672 p hg
    simpa only [d8136, d833, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48674 (p : Pattern) (guard : d8142 p = 1) : d835 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d835, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48673 p hg
    simpa only [d8142, d835, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d835, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d835, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48675 (p : Pattern) (guard : d8143 p = 1) : d836 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d836, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48668 p hg
    simpa only [d8143, d836, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d836, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48674 p hg
    simpa only [d8143, d836, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48676 (p : Pattern) (guard : d8144 p = 1) : d837 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d837, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48650 p hg
    simpa only [d8144, d837, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d837, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48675 p hg
    simpa only [d8144, d837, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48677 (p : Pattern) (guard : d8118 p = 1) : d372 p ≤ (0 : Int) + d372 p := by
  omega
theorem compare48678 (p : Pattern) (guard : d8119 p = 1) : d856 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d856, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35720 p hg
    simpa only [d8119, d856, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d856, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48677 p hg
    simpa only [d8119, d856, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48679 (p : Pattern) (guard : d8118 p = 1) : d857 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d857, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48213 p hg
    simpa only [d8118, d857, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d857, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38299 p hg
    simpa only [d8118, d857, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48680 (p : Pattern) (guard : d8124 p = 1) : d858 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d858, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48679 p hg
    simpa only [d8124, d858, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d858, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d858, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48681 (p : Pattern) (guard : d8125 p = 1) : d859 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d859, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48678 p hg
    simpa only [d8125, d859, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d859, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48680 p hg
    simpa only [d8125, d859, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48682 (p : Pattern) (guard : d8124 p = 1) : d912 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d912, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35766 p hg
    simpa only [d8124, d912, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d912, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35856 p hg
    simpa only [d8124, d912, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48683 (p : Pattern) (guard : d8123 p = 1) : d864 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d864, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48234 p hg
    simpa only [d8123, d864, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d864, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6535 p hg
    simpa only [d8123, d864, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48684 (p : Pattern) (guard : d8129 p = 1) : d865 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d865, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48683 p hg
    simpa only [d8129, d865, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d865, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d865, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48685 (p : Pattern) (guard : d8130 p = 1) : d913 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d913, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48682 p hg
    simpa only [d8130, d913, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d913, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48684 p hg
    simpa only [d8130, d913, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48686 (p : Pattern) (guard : d8131 p = 1) : d914 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d914, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48681 p hg
    simpa only [d8131, d914, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d914, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48685 p hg
    simpa only [d8131, d914, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48687 (p : Pattern) (guard : d8124 p = 1) : d868 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d868, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35787 p hg
    simpa only [d8124, d868, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d868, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48552 p hg
    simpa only [d8124, d868, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48688 (p : Pattern) (guard : d8130 p = 1) : d871 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d871, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48687 p hg
    simpa only [d8130, d871, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d871, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48560 p hg
    simpa only [d8130, d871, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48689 (p : Pattern) (guard : d8129 p = 1) : d915 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d915, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35799 p hg
    simpa only [d8129, d915, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d915, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d915, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48690 (p : Pattern) (guard : d8135 p = 1) : d916 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d916, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48689 p hg
    simpa only [d8135, d916, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d916, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7039 p hg
    simpa only [d8135, d916, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48691 (p : Pattern) (guard : d8136 p = 1) : d917 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d917, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48688 p hg
    simpa only [d8136, d917, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d917, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48690 p hg
    simpa only [d8136, d917, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48692 (p : Pattern) (guard : d8137 p = 1) : d918 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d918, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48686 p hg
    simpa only [d8137, d918, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d918, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48691 p hg
    simpa only [d8137, d918, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48693 (p : Pattern) (guard : d8124 p = 1) : d879 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d879, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38296 p hg
    simpa only [d8124, d879, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d879, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48655 p hg
    simpa only [d8124, d879, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48694 (p : Pattern) (guard : d8123 p = 1) : d869 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d869, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48249 p hg
    simpa only [d8123, d869, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d869, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6544 p hg
    simpa only [d8123, d869, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48695 (p : Pattern) (guard : d8129 p = 1) : d870 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d870, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48694 p hg
    simpa only [d8129, d870, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d870, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d870, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48696 (p : Pattern) (guard : d8130 p = 1) : d880 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d880, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48693 p hg
    simpa only [d8130, d880, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d880, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48695 p hg
    simpa only [d8130, d880, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48697 (p : Pattern) (guard : d8129 p = 1) : d915 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d915, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41508 p hg
    simpa only [d8129, d915, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d915, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d915, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48698 (p : Pattern) (guard : d8135 p = 1) : d916 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d916, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48697 p hg
    simpa only [d8135, d916, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d916, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7039 p hg
    simpa only [d8135, d916, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48699 (p : Pattern) (guard : d8136 p = 1) : d919 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d919, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48696 p hg
    simpa only [d8136, d919, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d919, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48698 p hg
    simpa only [d8136, d919, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48700 (p : Pattern) (guard : d8142 p = 1) : d920 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d920, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48699 p hg
    simpa only [d8142, d920, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d920, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38307 p hg
    simpa only [d8142, d920, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48701 (p : Pattern) (guard : d8143 p = 1) : d921 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d921, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48692 p hg
    simpa only [d8143, d921, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d921, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48700 p hg
    simpa only [d8143, d921, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48702 (p : Pattern) (guard : d8124 p = 1) : d884 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d884, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35823 p hg
    simpa only [d8124, d884, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d884, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48297 p hg
    simpa only [d8124, d884, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48703 (p : Pattern) (guard : d8123 p = 1) : d922 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d922, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48261 p hg
    simpa only [d8123, d922, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d922, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6544 p hg
    simpa only [d8123, d922, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48704 (p : Pattern) (guard : d8129 p = 1) : d923 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d923, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48703 p hg
    simpa only [d8129, d923, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d923, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d923, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48705 (p : Pattern) (guard : d8130 p = 1) : d924 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d924, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48702 p hg
    simpa only [d8130, d924, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d924, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48704 p hg
    simpa only [d8130, d924, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48706 (p : Pattern) (guard : d8129 p = 1) : d915 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d915, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35841 p hg
    simpa only [d8129, d915, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d915, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38315 p hg
    simpa only [d8129, d915, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48707 (p : Pattern) (guard : d8135 p = 1) : d928 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d928, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48706 p hg
    simpa only [d8135, d928, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d928, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7097 p hg
    simpa only [d8135, d928, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48708 (p : Pattern) (guard : d8136 p = 1) : d929 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d929, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48705 p hg
    simpa only [d8136, d929, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d929, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48707 p hg
    simpa only [d8136, d929, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48709 (p : Pattern) (guard : d8129 p = 1) : d930 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d930, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41522 p hg
    simpa only [d8129, d930, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d930, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d930, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48710 (p : Pattern) (guard : d8135 p = 1) : d932 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d932, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48709 p hg
    simpa only [d8135, d932, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d932, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7101 p hg
    simpa only [d8135, d932, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48711 (p : Pattern) (guard : d0 p = 1) : d935 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48712 (p : Pattern) (guard : d8141 p = 1) : d936 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d936, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48710 p hg
    simpa only [d8141, d936, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d936, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48711 p hg
    simpa only [d8141, d936, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48713 (p : Pattern) (guard : d8142 p = 1) : d937 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d937, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48708 p hg
    simpa only [d8142, d937, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d937, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48712 p hg
    simpa only [d8142, d937, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48714 (p : Pattern) (guard : d8129 p = 1) : d938 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d938, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41529 p hg
    simpa only [d8129, d938, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d938, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d938, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48715 (p : Pattern) (guard : d8135 p = 1) : d941 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d941, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48714 p hg
    simpa only [d8135, d941, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d941, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7111 p hg
    simpa only [d8135, d941, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48716 (p : Pattern) (guard : d0 p = 1) : d935 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48717 (p : Pattern) (guard : d8141 p = 1) : d942 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d942, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48715 p hg
    simpa only [d8141, d942, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d942, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48716 p hg
    simpa only [d8141, d942, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48718 (p : Pattern) (guard : d8147 p = 1) : d943 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8141 p = 1 := by simpa only [d8147, d943, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48717 p hg
    simpa only [d8147, d943, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8147, d943, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8147, d943, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48719 (p : Pattern) (guard : d8148 p = 1) : d944 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d944, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48713 p hg
    simpa only [d8148, d944, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d944, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48718 p hg
    simpa only [d8148, d944, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
