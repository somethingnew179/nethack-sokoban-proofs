/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons243
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare34160 (p : Pattern) (guard : d8117 p = 1) : d0 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34150 p hg
    simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34161 (p : Pattern) (guard : d8118 p = 1) : d0 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34143 p hg
    simpa only [d8118, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34160 p hg
    simpa only [d8118, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34162 (p : Pattern) (guard : d8124 p = 1) : d0 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34161 p hg
    simpa only [d8124, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34057 p hg
    simpa only [d8124, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34163 (p : Pattern) (guard : d8130 p = 1) : d0 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34162 p hg
    simpa only [d8130, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34059 p hg
    simpa only [d8130, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34164 (p : Pattern) (guard : d8131 p = 1) : d0 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34101 p hg
    simpa only [d8131, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34163 p hg
    simpa only [d8131, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34165 (p : Pattern) (guard : d8135 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34166 (p : Pattern) (guard : d8136 p = 1) : d0 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34065 p hg
    simpa only [d8136, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34165 p hg
    simpa only [d8136, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34167 (p : Pattern) (guard : d8137 p = 1) : d0 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34164 p hg
    simpa only [d8137, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34166 p hg
    simpa only [d8137, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34168 (p : Pattern) (guard : d8138 p = 1) : d0 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34159 p hg
    simpa only [d8138, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34167 p hg
    simpa only [d8138, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34169 (p : Pattern) (guard : d8107 p = 1) : d0 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34117 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34136 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34170 (p : Pattern) (guard : d8113 p = 1) : d0 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34169 p hg
    simpa only [d8113, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34151 p hg
    simpa only [d8113, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34171 (p : Pattern) (guard : d8119 p = 1) : d0 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34170 p hg
    simpa only [d8119, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34104 p hg
    simpa only [d8119, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34172 (p : Pattern) (guard : d8125 p = 1) : d0 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34171 p hg
    simpa only [d8125, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34064 p hg
    simpa only [d8125, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34173 (p : Pattern) (guard : d5843 p = 1) : d0 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1518 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34174 (p : Pattern) (guard : d5847 p = 1) : d0 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34173 p hg
    simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5847, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34175 (p : Pattern) (guard : d5854 p = 1) : d0 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34174 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34176 (p : Pattern) (guard : d8099 p = 1) : d0 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34175 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34177 (p : Pattern) (guard : d8105 p = 1) : d0 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34176 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34178 (p : Pattern) (guard : d8111 p = 1) : d0 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34177 p hg
    simpa only [d8111, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8111, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34179 (p : Pattern) (guard : d8112 p = 1) : d0 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34130 p hg
    simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34178 p hg
    simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34180 (p : Pattern) (guard : d8117 p = 1) : d0 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34142 p hg
    simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34181 (p : Pattern) (guard : d8118 p = 1) : d0 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34179 p hg
    simpa only [d8118, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34180 p hg
    simpa only [d8118, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34182 (p : Pattern) (guard : d8123 p = 1) : d0 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34160 p hg
    simpa only [d8123, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8123, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34183 (p : Pattern) (guard : d8124 p = 1) : d0 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34181 p hg
    simpa only [d8124, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34182 p hg
    simpa only [d8124, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34184 (p : Pattern) (guard : d8130 p = 1) : d0 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34183 p hg
    simpa only [d8130, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34059 p hg
    simpa only [d8130, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34185 (p : Pattern) (guard : d8131 p = 1) : d0 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34172 p hg
    simpa only [d8131, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34184 p hg
    simpa only [d8131, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34186 (p : Pattern) (guard : d8129 p = 1) : d0 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34182 p hg
    simpa only [d8129, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8129, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34187 (p : Pattern) (guard : d8135 p = 1) : d0 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34186 p hg
    simpa only [d8135, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8135, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34188 (p : Pattern) (guard : d8136 p = 1) : d0 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34106 p hg
    simpa only [d8136, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34187 p hg
    simpa only [d8136, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34189 (p : Pattern) (guard : d8137 p = 1) : d0 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34185 p hg
    simpa only [d8137, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34188 p hg
    simpa only [d8137, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34190 (p : Pattern) (guard : d8123 p = 1) : d0 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34180 p hg
    simpa only [d8123, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8123, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34191 (p : Pattern) (guard : d8129 p = 1) : d0 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34190 p hg
    simpa only [d8129, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8129, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34192 (p : Pattern) (guard : d8135 p = 1) : d0 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34191 p hg
    simpa only [d8135, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8135, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34193 (p : Pattern) (guard : d8136 p = 1) : d0 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34157 p hg
    simpa only [d8136, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34192 p hg
    simpa only [d8136, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34194 (p : Pattern) (guard : d8141 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34195 (p : Pattern) (guard : d8142 p = 1) : d0 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34193 p hg
    simpa only [d8142, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34194 p hg
    simpa only [d8142, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34196 (p : Pattern) (guard : d8143 p = 1) : d0 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34189 p hg
    simpa only [d8143, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34195 p hg
    simpa only [d8143, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34197 (p : Pattern) (guard : d8144 p = 1) : d0 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34168 p hg
    simpa only [d8144, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34196 p hg
    simpa only [d8144, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34198 (p : Pattern) (guard : d8145 p = 1) : d0 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34110 p hg
    simpa only [d8145, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34197 p hg
    simpa only [d8145, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34199 (p : Pattern) (guard : d8146 p = 1) : d0 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34071 p hg
    simpa only [d8146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34198 p hg
    simpa only [d8146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34200 (p : Pattern) (guard : d8086 p = 1) : d0 p ≤ (0 : Int) + d319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33798 p hg
    simpa only [d8086, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34000 p hg
    simpa only [d8086, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34201 (p : Pattern) (guard : d8091 p = 1) : d0 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34200 p hg
    simpa only [d8091, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33956 p hg
    simpa only [d8091, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34202 (p : Pattern) (guard : d8096 p = 1) : d0 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34201 p hg
    simpa only [d8096, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34002 p hg
    simpa only [d8096, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34203 (p : Pattern) (guard : d8102 p = 1) : d0 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34202 p hg
    simpa only [d8102, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34125 p hg
    simpa only [d8102, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34204 (p : Pattern) (guard : d8108 p = 1) : d0 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34203 p hg
    simpa only [d8108, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34169 p hg
    simpa only [d8108, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34205 (p : Pattern) (guard : d8114 p = 1) : d0 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34204 p hg
    simpa only [d8114, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34099 p hg
    simpa only [d8114, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34206 (p : Pattern) (guard : d8120 p = 1) : d0 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34205 p hg
    simpa only [d8120, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34054 p hg
    simpa only [d8120, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34207 (p : Pattern) (guard : d8085 p = 1) : d0 p ≤ (0 : Int) + d380 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33880 p hg
    simpa only [d8085, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34005 p hg
    simpa only [d8085, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34208 (p : Pattern) (guard : d8090 p = 1) : d0 p ≤ (0 : Int) + d381 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34207 p hg
    simpa only [d8090, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34045 p hg
    simpa only [d8090, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34209 (p : Pattern) (guard : d8095 p = 1) : d0 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34208 p hg
    simpa only [d8095, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34009 p hg
    simpa only [d8095, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34210 (p : Pattern) (guard : d8101 p = 1) : d0 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34209 p hg
    simpa only [d8101, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34047 p hg
    simpa only [d8101, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34211 (p : Pattern) (guard : d8084 p = 1) : d0 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33842 p hg
    simpa only [d8084, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34004 p hg
    simpa only [d8084, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34212 (p : Pattern) (guard : d8089 p = 1) : d0 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34211 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34006 p hg
    simpa only [d8089, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34213 (p : Pattern) (guard : d8094 p = 1) : d0 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34212 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34008 p hg
    simpa only [d8094, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34214 (p : Pattern) (guard : d8100 p = 1) : d0 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34213 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d8100, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34215 (p : Pattern) (guard : d8106 p = 1) : d0 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34214 p hg
    simpa only [d8106, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34012 p hg
    simpa only [d8106, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34216 (p : Pattern) (guard : d8107 p = 1) : d0 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34210 p hg
    simpa only [d8107, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34215 p hg
    simpa only [d8107, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34217 (p : Pattern) (guard : d8113 p = 1) : d0 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34216 p hg
    simpa only [d8113, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34179 p hg
    simpa only [d8113, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34218 (p : Pattern) (guard : d8119 p = 1) : d0 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34217 p hg
    simpa only [d8119, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34161 p hg
    simpa only [d8119, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34219 (p : Pattern) (guard : d8125 p = 1) : d0 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34218 p hg
    simpa only [d8125, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34156 p hg
    simpa only [d8125, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34220 (p : Pattern) (guard : d8126 p = 1) : d0 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34206 p hg
    simpa only [d8126, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34219 p hg
    simpa only [d8126, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34221 (p : Pattern) (guard : d8132 p = 1) : d0 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34220 p hg
    simpa only [d8132, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34164 p hg
    simpa only [d8132, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34222 (p : Pattern) (guard : d8138 p = 1) : d0 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34221 p hg
    simpa only [d8138, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34189 p hg
    simpa only [d8138, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34223 (p : Pattern) (guard : d5843 p = 1) : d0 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4499 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5843, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34224 (p : Pattern) (guard : d5847 p = 1) : d0 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34223 p hg
    simpa only [d5847, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5847, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34225 (p : Pattern) (guard : d5854 p = 1) : d0 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34224 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34226 (p : Pattern) (guard : d8099 p = 1) : d0 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34225 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8099, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34227 (p : Pattern) (guard : d8105 p = 1) : d0 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34226 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8105, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34228 (p : Pattern) (guard : d8111 p = 1) : d0 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34227 p hg
    simpa only [d8111, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8111, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34229 (p : Pattern) (guard : d8112 p = 1) : d0 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34215 p hg
    simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34228 p hg
    simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34230 (p : Pattern) (guard : d8117 p = 1) : d0 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34178 p hg
    simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34231 (p : Pattern) (guard : d8118 p = 1) : d0 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34229 p hg
    simpa only [d8118, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34230 p hg
    simpa only [d8118, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34232 (p : Pattern) (guard : d8124 p = 1) : d0 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34231 p hg
    simpa only [d8124, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34190 p hg
    simpa only [d8124, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34233 (p : Pattern) (guard : d8130 p = 1) : d0 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34232 p hg
    simpa only [d8130, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34186 p hg
    simpa only [d8130, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34234 (p : Pattern) (guard : d8131 p = 1) : d0 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34154 p hg
    simpa only [d8131, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34233 p hg
    simpa only [d8131, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34235 (p : Pattern) (guard : d8137 p = 1) : d0 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34234 p hg
    simpa only [d8137, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34193 p hg
    simpa only [d8137, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34236 (p : Pattern) (guard : d8123 p = 1) : d0 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34230 p hg
    simpa only [d8123, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8123, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34237 (p : Pattern) (guard : d8129 p = 1) : d0 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34236 p hg
    simpa only [d8129, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8129, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34238 (p : Pattern) (guard : d8135 p = 1) : d0 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34237 p hg
    simpa only [d8135, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8135, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34239 (p : Pattern) (guard : d8136 p = 1) : d0 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34163 p hg
    simpa only [d8136, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34238 p hg
    simpa only [d8136, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34240 (p : Pattern) (guard : d8142 p = 1) : d0 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34239 p hg
    simpa only [d8142, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34194 p hg
    simpa only [d8142, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34241 (p : Pattern) (guard : d8143 p = 1) : d0 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34235 p hg
    simpa only [d8143, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34240 p hg
    simpa only [d8143, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34242 (p : Pattern) (guard : d8144 p = 1) : d0 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34222 p hg
    simpa only [d8144, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34241 p hg
    simpa only [d8144, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34243 (p : Pattern) (guard : d8085 p = 1) : d0 p ≤ (0 : Int) + d430 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33980 p hg
    simpa only [d8085, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34044 p hg
    simpa only [d8085, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34244 (p : Pattern) (guard : d8090 p = 1) : d0 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34243 p hg
    simpa only [d8090, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34093 p hg
    simpa only [d8090, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34245 (p : Pattern) (guard : d8095 p = 1) : d0 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34244 p hg
    simpa only [d8095, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34046 p hg
    simpa only [d8095, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34246 (p : Pattern) (guard : d8101 p = 1) : d0 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34245 p hg
    simpa only [d8101, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34095 p hg
    simpa only [d8101, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34247 (p : Pattern) (guard : d8084 p = 1) : d0 p ≤ (0 : Int) + d339 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d8084, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34004 p hg
    simpa only [d8084, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34248 (p : Pattern) (guard : d8089 p = 1) : d0 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34247 p hg
    simpa only [d8089, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34006 p hg
    simpa only [d8089, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34249 (p : Pattern) (guard : d8094 p = 1) : d0 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34248 p hg
    simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34147 p hg
    simpa only [d8094, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34250 (p : Pattern) (guard : d8100 p = 1) : d0 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34249 p hg
    simpa only [d8100, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d8100, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34251 (p : Pattern) (guard : d8106 p = 1) : d0 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34250 p hg
    simpa only [d8106, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34149 p hg
    simpa only [d8106, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34252 (p : Pattern) (guard : d8107 p = 1) : d0 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34246 p hg
    simpa only [d8107, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34251 p hg
    simpa only [d8107, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34253 (p : Pattern) (guard : d8113 p = 1) : d0 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34252 p hg
    simpa only [d8113, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34229 p hg
    simpa only [d8113, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34254 (p : Pattern) (guard : d8119 p = 1) : d0 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34253 p hg
    simpa only [d8119, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34181 p hg
    simpa only [d8119, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34255 (p : Pattern) (guard : d8125 p = 1) : d0 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34254 p hg
    simpa only [d8125, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34162 p hg
    simpa only [d8125, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34256 (p : Pattern) (guard : d8084 p = 1) : d0 p ≤ (0 : Int) + d326 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33810 p hg
    simpa only [d8084, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34145 p hg
    simpa only [d8084, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34257 (p : Pattern) (guard : d8089 p = 1) : d0 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34256 p hg
    simpa only [d8089, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34146 p hg
    simpa only [d8089, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34258 (p : Pattern) (guard : d8094 p = 1) : d0 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34257 p hg
    simpa only [d8094, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34139 p hg
    simpa only [d8094, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34259 (p : Pattern) (guard : d8100 p = 1) : d0 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34258 p hg
    simpa only [d8100, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34148 p hg
    simpa only [d8100, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34260 (p : Pattern) (guard : d8106 p = 1) : d0 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34259 p hg
    simpa only [d8106, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34141 p hg
    simpa only [d8106, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34261 (p : Pattern) (guard : d5843 p = 1) : d0 p ≤ (0 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1487 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5843, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34262 (p : Pattern) (guard : d5847 p = 1) : d0 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34261 p hg
    simpa only [d5847, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5847, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34263 (p : Pattern) (guard : d5854 p = 1) : d0 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34262 p hg
    simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5854, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34264 (p : Pattern) (guard : d8099 p = 1) : d0 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34263 p hg
    simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8099, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34265 (p : Pattern) (guard : d8105 p = 1) : d0 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34264 p hg
    simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8105, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34266 (p : Pattern) (guard : d8111 p = 1) : d0 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34265 p hg
    simpa only [d8111, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8111, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34267 (p : Pattern) (guard : d8112 p = 1) : d0 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34260 p hg
    simpa only [d8112, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34266 p hg
    simpa only [d8112, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34268 (p : Pattern) (guard : d5843 p = 1) : d0 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare905 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5843, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34269 (p : Pattern) (guard : d5847 p = 1) : d0 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34268 p hg
    simpa only [d5847, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5847, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34270 (p : Pattern) (guard : d5854 p = 1) : d0 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34269 p hg
    simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5854, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34271 (p : Pattern) (guard : d8099 p = 1) : d0 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34270 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8099, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34272 (p : Pattern) (guard : d8105 p = 1) : d0 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34271 p hg
    simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8105, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34273 (p : Pattern) (guard : d8111 p = 1) : d0 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34272 p hg
    simpa only [d8111, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8111, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34274 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34275 (p : Pattern) (guard : d8117 p = 1) : d0 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34273 p hg
    simpa only [d8117, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34274 p hg
    simpa only [d8117, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34276 (p : Pattern) (guard : d8118 p = 1) : d0 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34267 p hg
    simpa only [d8118, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34275 p hg
    simpa only [d8118, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34277 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34278 (p : Pattern) (guard : d8117 p = 1) : d0 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34228 p hg
    simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34277 p hg
    simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34279 (p : Pattern) (guard : d8123 p = 1) : d0 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34278 p hg
    simpa only [d8123, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8123, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34280 (p : Pattern) (guard : d8124 p = 1) : d0 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34276 p hg
    simpa only [d8124, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34279 p hg
    simpa only [d8124, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34281 (p : Pattern) (guard : d8130 p = 1) : d0 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34280 p hg
    simpa only [d8130, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34237 p hg
    simpa only [d8130, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34282 (p : Pattern) (guard : d8131 p = 1) : d0 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34255 p hg
    simpa only [d8131, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34281 p hg
    simpa only [d8131, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34283 (p : Pattern) (guard : d8129 p = 1) : d0 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34279 p hg
    simpa only [d8129, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8129, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34284 (p : Pattern) (guard : d8135 p = 1) : d0 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34283 p hg
    simpa only [d8135, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8135, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34285 (p : Pattern) (guard : d8136 p = 1) : d0 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34184 p hg
    simpa only [d8136, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34284 p hg
    simpa only [d8136, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34286 (p : Pattern) (guard : d8137 p = 1) : d0 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34282 p hg
    simpa only [d8137, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34285 p hg
    simpa only [d8137, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34287 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34288 (p : Pattern) (guard : d8123 p = 1) : d0 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34275 p hg
    simpa only [d8123, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34287 p hg
    simpa only [d8123, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34289 (p : Pattern) (guard : d8129 p = 1) : d0 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34288 p hg
    simpa only [d8129, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8129, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34290 (p : Pattern) (guard : d8135 p = 1) : d0 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34289 p hg
    simpa only [d8135, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8135, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34291 (p : Pattern) (guard : d8136 p = 1) : d0 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34233 p hg
    simpa only [d8136, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34290 p hg
    simpa only [d8136, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34292 (p : Pattern) (guard : d8141 p = 1) : d0 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34192 p hg
    simpa only [d8141, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8141, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34293 (p : Pattern) (guard : d8142 p = 1) : d0 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34291 p hg
    simpa only [d8142, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34292 p hg
    simpa only [d8142, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34294 (p : Pattern) (guard : d8143 p = 1) : d0 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34286 p hg
    simpa only [d8143, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34293 p hg
    simpa only [d8143, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34295 (p : Pattern) (guard : d8112 p = 1) : d0 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34251 p hg
    simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34273 p hg
    simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34296 (p : Pattern) (guard : d8118 p = 1) : d0 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34295 p hg
    simpa only [d8118, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34278 p hg
    simpa only [d8118, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34297 (p : Pattern) (guard : d8124 p = 1) : d0 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34296 p hg
    simpa only [d8124, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34236 p hg
    simpa only [d8124, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34298 (p : Pattern) (guard : d8130 p = 1) : d0 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34297 p hg
    simpa only [d8130, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34191 p hg
    simpa only [d8130, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34299 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d360 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
