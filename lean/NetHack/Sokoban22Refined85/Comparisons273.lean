/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons272
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare38220 (p : Pattern) (guard : d8136 p = 1) : d162 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d162, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38219 p hg
    simpa only [d8136, d162, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d162, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37270 p hg
    simpa only [d8136, d162, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38221 (p : Pattern) (guard : d8137 p = 1) : d684 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d684, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38216 p hg
    simpa only [d8137, d684, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d684, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38220 p hg
    simpa only [d8137, d684, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38222 (p : Pattern) (guard : d8138 p = 1) : d685 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d685, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38200 p hg
    simpa only [d8138, d685, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d685, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38221 p hg
    simpa only [d8138, d685, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38223 (p : Pattern) (guard : d8130 p = 1) : d407 p ≤ (0 : Int) + d407 p := by
  omega
theorem compare38224 (p : Pattern) (guard : d8131 p = 1) : d686 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d686, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35324 p hg
    simpa only [d8131, d686, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d686, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38223 p hg
    simpa only [d8131, d686, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38225 (p : Pattern) (guard : d8135 p = 1) : d411 p ≤ (0 : Int) + d411 p := by
  omega
theorem compare38226 (p : Pattern) (guard : d8136 p = 1) : d687 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d687, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35364 p hg
    simpa only [d8136, d687, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d687, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38225 p hg
    simpa only [d8136, d687, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38227 (p : Pattern) (guard : d8137 p = 1) : d688 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d688, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38224 p hg
    simpa only [d8137, d688, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d688, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38226 p hg
    simpa only [d8137, d688, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38228 (p : Pattern) (guard : d8112 p = 1) : d105 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35276 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35370 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38229 (p : Pattern) (guard : d8118 p = 1) : d111 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d111, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38228 p hg
    simpa only [d8118, d111, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d111, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35356 p hg
    simpa only [d8118, d111, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38230 (p : Pattern) (guard : d8124 p = 1) : d114 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d114, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38229 p hg
    simpa only [d8124, d114, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d114, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35358 p hg
    simpa only [d8124, d114, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38231 (p : Pattern) (guard : d8130 p = 1) : d152 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d152, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38230 p hg
    simpa only [d8130, d152, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d152, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35363 p hg
    simpa only [d8130, d152, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38232 (p : Pattern) (guard : d8135 p = 1) : d421 p ≤ (0 : Int) + d421 p := by
  omega
theorem compare38233 (p : Pattern) (guard : d8136 p = 1) : d689 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d689, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38231 p hg
    simpa only [d8136, d689, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d689, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38232 p hg
    simpa only [d8136, d689, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38234 (p : Pattern) (guard : d8142 p = 1) : d690 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d690, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38233 p hg
    simpa only [d8142, d690, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d690, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d690, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38235 (p : Pattern) (guard : d8143 p = 1) : d691 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d691, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38227 p hg
    simpa only [d8143, d691, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d691, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38234 p hg
    simpa only [d8143, d691, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38236 (p : Pattern) (guard : d8144 p = 1) : d692 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d692, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38222 p hg
    simpa only [d8144, d692, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d692, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38235 p hg
    simpa only [d8144, d692, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38237 (p : Pattern) (guard : d8145 p = 1) : d693 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d693, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38195 p hg
    simpa only [d8145, d693, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d693, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38236 p hg
    simpa only [d8145, d693, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38238 (p : Pattern) (guard : d8146 p = 1) : d694 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38168 p hg
    simpa only [d8146, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38237 p hg
    simpa only [d8146, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38239 (p : Pattern) (guard : d8126 p = 1) : d667 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d667, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35410 p hg
    simpa only [d8126, d667, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d667, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38196 p hg
    simpa only [d8126, d667, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38240 (p : Pattern) (guard : d8131 p = 1) : d668 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d668, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35461 p hg
    simpa only [d8131, d668, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d668, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38198 p hg
    simpa only [d8131, d668, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38241 (p : Pattern) (guard : d8132 p = 1) : d669 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d669, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38239 p hg
    simpa only [d8132, d669, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d669, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38240 p hg
    simpa only [d8132, d669, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38242 (p : Pattern) (guard : d8131 p = 1) : d654 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d654, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35623 p hg
    simpa only [d8131, d654, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d654, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38215 p hg
    simpa only [d8131, d654, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38243 (p : Pattern) (guard : d8112 p = 1) : d89 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d89, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34798 p hg
    simpa only [d8112, d89, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d89, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34729 p hg
    simpa only [d8112, d89, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38244 (p : Pattern) (guard : d8118 p = 1) : d90 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d90, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38243 p hg
    simpa only [d8118, d90, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d90, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d90, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38245 (p : Pattern) (guard : d8123 p = 1) : d91 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8123, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38246 (p : Pattern) (guard : d8124 p = 1) : d92 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d92, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38244 p hg
    simpa only [d8124, d92, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d92, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38245 p hg
    simpa only [d8124, d92, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38247 (p : Pattern) (guard : d8129 p = 1) : d93 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38245 p hg
    simpa only [d8129, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38248 (p : Pattern) (guard : d8130 p = 1) : d94 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d94, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38246 p hg
    simpa only [d8130, d94, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d94, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38247 p hg
    simpa only [d8130, d94, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38249 (p : Pattern) (guard : d8136 p = 1) : d670 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d670, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38248 p hg
    simpa only [d8136, d670, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d670, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37270 p hg
    simpa only [d8136, d670, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38250 (p : Pattern) (guard : d8137 p = 1) : d671 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d671, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38242 p hg
    simpa only [d8137, d671, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d671, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38249 p hg
    simpa only [d8137, d671, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38251 (p : Pattern) (guard : d8138 p = 1) : d672 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d672, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38241 p hg
    simpa only [d8138, d672, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d672, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38250 p hg
    simpa only [d8138, d672, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38252 (p : Pattern) (guard : d8131 p = 1) : d673 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d673, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35508 p hg
    simpa only [d8131, d673, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d673, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38223 p hg
    simpa only [d8131, d673, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38253 (p : Pattern) (guard : d8136 p = 1) : d674 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d674, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35548 p hg
    simpa only [d8136, d674, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d674, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38225 p hg
    simpa only [d8136, d674, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38254 (p : Pattern) (guard : d8137 p = 1) : d675 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d675, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38252 p hg
    simpa only [d8137, d675, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d675, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38253 p hg
    simpa only [d8137, d675, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38255 (p : Pattern) (guard : d8136 p = 1) : d661 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d661, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35681 p hg
    simpa only [d8136, d661, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d661, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38232 p hg
    simpa only [d8136, d661, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38256 (p : Pattern) (guard : d8142 p = 1) : d676 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d676, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38255 p hg
    simpa only [d8142, d676, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d676, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d676, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38257 (p : Pattern) (guard : d8143 p = 1) : d677 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d677, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38254 p hg
    simpa only [d8143, d677, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d677, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38256 p hg
    simpa only [d8143, d677, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38258 (p : Pattern) (guard : d8144 p = 1) : d678 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d678, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38251 p hg
    simpa only [d8144, d678, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d678, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38257 p hg
    simpa only [d8144, d678, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38259 (p : Pattern) (guard : d8145 p = 1) : d679 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d679, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38195 p hg
    simpa only [d8145, d679, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d679, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38258 p hg
    simpa only [d8145, d679, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38260 (p : Pattern) (guard : d8125 p = 1) : d392 p ≤ (0 : Int) + d392 p := by
  omega
theorem compare38261 (p : Pattern) (guard : d8126 p = 1) : d653 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d653, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35582 p hg
    simpa only [d8126, d653, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d653, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38260 p hg
    simpa only [d8126, d653, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38262 (p : Pattern) (guard : d8132 p = 1) : d655 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d655, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38261 p hg
    simpa only [d8132, d655, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d655, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38242 p hg
    simpa only [d8132, d655, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38263 (p : Pattern) (guard : d8112 p = 1) : d79 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d79, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35019 p hg
    simpa only [d8112, d79, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d79, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34918 p hg
    simpa only [d8112, d79, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38264 (p : Pattern) (guard : d8118 p = 1) : d80 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d80, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38263 p hg
    simpa only [d8118, d80, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d80, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d80, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38265 (p : Pattern) (guard : d8124 p = 1) : d81 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d81, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38264 p hg
    simpa only [d8124, d81, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d81, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d81, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38266 (p : Pattern) (guard : d8125 p = 1) : d82 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d82, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35496 p hg
    simpa only [d8125, d82, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d82, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38265 p hg
    simpa only [d8125, d82, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38267 (p : Pattern) (guard : d8131 p = 1) : d656 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d656, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38266 p hg
    simpa only [d8131, d656, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d656, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38223 p hg
    simpa only [d8131, d656, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38268 (p : Pattern) (guard : d8112 p = 1) : d89 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d89, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34982 p hg
    simpa only [d8112, d89, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d89, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34729 p hg
    simpa only [d8112, d89, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38269 (p : Pattern) (guard : d8118 p = 1) : d90 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d90, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38268 p hg
    simpa only [d8118, d90, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d90, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d90, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38270 (p : Pattern) (guard : d8124 p = 1) : d92 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d92, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38269 p hg
    simpa only [d8124, d92, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d92, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38245 p hg
    simpa only [d8124, d92, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38271 (p : Pattern) (guard : d8130 p = 1) : d94 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d94, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38270 p hg
    simpa only [d8130, d94, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d94, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38247 p hg
    simpa only [d8130, d94, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38272 (p : Pattern) (guard : d8136 p = 1) : d657 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d657, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38271 p hg
    simpa only [d8136, d657, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d657, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38225 p hg
    simpa only [d8136, d657, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38273 (p : Pattern) (guard : d8137 p = 1) : d658 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d658, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38267 p hg
    simpa only [d8137, d658, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d658, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38272 p hg
    simpa only [d8137, d658, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38274 (p : Pattern) (guard : d8138 p = 1) : d659 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d659, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38262 p hg
    simpa only [d8138, d659, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d659, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38273 p hg
    simpa only [d8138, d659, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38275 (p : Pattern) (guard : d8131 p = 1) : d660 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d660, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35648 p hg
    simpa only [d8131, d660, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d660, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35804 p hg
    simpa only [d8131, d660, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38276 (p : Pattern) (guard : d8137 p = 1) : d662 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d662, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38275 p hg
    simpa only [d8137, d662, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d662, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38255 p hg
    simpa only [d8137, d662, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38277 (p : Pattern) (guard : d8112 p = 1) : d16 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35484 p hg
    simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35686 p hg
    simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38278 (p : Pattern) (guard : d8117 p = 1) : d21 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d21, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35553 p hg
    simpa only [d8117, d21, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d21, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3640 p hg
    simpa only [d8117, d21, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38279 (p : Pattern) (guard : d8118 p = 1) : d22 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d22, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38277 p hg
    simpa only [d8118, d22, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d22, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38278 p hg
    simpa only [d8118, d22, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38280 (p : Pattern) (guard : d8124 p = 1) : d29 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d29, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38279 p hg
    simpa only [d8124, d29, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d29, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35543 p hg
    simpa only [d8124, d29, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38281 (p : Pattern) (guard : d8130 p = 1) : d82 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d82, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38280 p hg
    simpa only [d8130, d82, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d82, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35547 p hg
    simpa only [d8130, d82, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38282 (p : Pattern) (guard : d8135 p = 1) : d410 p ≤ (0 : Int) + d410 p := by
  omega
theorem compare38283 (p : Pattern) (guard : d8136 p = 1) : d663 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d663, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38281 p hg
    simpa only [d8136, d663, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d663, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38282 p hg
    simpa only [d8136, d663, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38284 (p : Pattern) (guard : d8142 p = 1) : d664 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d664, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38283 p hg
    simpa only [d8142, d664, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d664, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d664, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38285 (p : Pattern) (guard : d8143 p = 1) : d665 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d665, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38276 p hg
    simpa only [d8143, d665, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d665, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38284 p hg
    simpa only [d8143, d665, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38286 (p : Pattern) (guard : d8144 p = 1) : d666 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d666, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38274 p hg
    simpa only [d8144, d666, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d666, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38285 p hg
    simpa only [d8144, d666, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38287 (p : Pattern) (guard : d8112 p = 1) : d415 p ≤ (0 : Int) + d415 p := by
  omega
theorem compare38288 (p : Pattern) (guard : d8118 p = 1) : d449 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d449, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38287 p hg
    simpa only [d8118, d449, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d449, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35806 p hg
    simpa only [d8118, d449, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38289 (p : Pattern) (guard : d8124 p = 1) : d452 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d452, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38288 p hg
    simpa only [d8124, d452, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d452, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35856 p hg
    simpa only [d8124, d452, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38290 (p : Pattern) (guard : d8129 p = 1) : d409 p ≤ (0 : Int) + d409 p := by
  omega
theorem compare38291 (p : Pattern) (guard : d8130 p = 1) : d453 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d453, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38289 p hg
    simpa only [d8130, d453, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d453, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38290 p hg
    simpa only [d8130, d453, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38292 (p : Pattern) (guard : d8131 p = 1) : d695 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d695, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35743 p hg
    simpa only [d8131, d695, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d695, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38291 p hg
    simpa only [d8131, d695, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38293 (p : Pattern) (guard : d8136 p = 1) : d696 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d696, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35791 p hg
    simpa only [d8136, d696, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d696, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35858 p hg
    simpa only [d8136, d696, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38294 (p : Pattern) (guard : d8137 p = 1) : d697 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d697, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38292 p hg
    simpa only [d8137, d697, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d697, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38293 p hg
    simpa only [d8137, d697, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38295 (p : Pattern) (guard : d8112 p = 1) : d105 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35712 p hg
    simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35797 p hg
    simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38296 (p : Pattern) (guard : d8118 p = 1) : d111 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d111, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38295 p hg
    simpa only [d8118, d111, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d111, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35824 p hg
    simpa only [d8118, d111, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38297 (p : Pattern) (guard : d8123 p = 1) : d113 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d113, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35786 p hg
    simpa only [d8123, d113, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d113, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d8123, d113, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38298 (p : Pattern) (guard : d8124 p = 1) : d114 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d114, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38296 p hg
    simpa only [d8124, d114, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d114, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38297 p hg
    simpa only [d8124, d114, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38299 (p : Pattern) (guard : d8117 p = 1) : d149 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d149, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35283 p hg
    simpa only [d8117, d149, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d149, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3777 p hg
    simpa only [d8117, d149, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38300 (p : Pattern) (guard : d8123 p = 1) : d150 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d150, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38299 p hg
    simpa only [d8123, d150, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d150, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d150, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38301 (p : Pattern) (guard : d8129 p = 1) : d151 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d151, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38300 p hg
    simpa only [d8129, d151, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d151, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d151, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38302 (p : Pattern) (guard : d8130 p = 1) : d152 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d152, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38298 p hg
    simpa only [d8130, d152, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d152, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38301 p hg
    simpa only [d8130, d152, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38303 (p : Pattern) (guard : d8136 p = 1) : d698 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d698, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38302 p hg
    simpa only [d8136, d698, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d698, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35810 p hg
    simpa only [d8136, d698, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38304 (p : Pattern) (guard : d8123 p = 1) : d159 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d159, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35728 p hg
    simpa only [d8123, d159, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d159, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d159, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38305 (p : Pattern) (guard : d8129 p = 1) : d160 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d160, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38304 p hg
    simpa only [d8129, d160, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d160, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d160, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38306 (p : Pattern) (guard : d8135 p = 1) : d161 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d161, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38305 p hg
    simpa only [d8135, d161, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d161, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d161, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38307 (p : Pattern) (guard : d8141 p = 1) : d162 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d162, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38306 p hg
    simpa only [d8141, d162, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d162, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8141, d162, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38308 (p : Pattern) (guard : d8142 p = 1) : d699 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d699, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38303 p hg
    simpa only [d8142, d699, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d699, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38307 p hg
    simpa only [d8142, d699, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38309 (p : Pattern) (guard : d8143 p = 1) : d700 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d700, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38294 p hg
    simpa only [d8143, d700, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d700, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38308 p hg
    simpa only [d8143, d700, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38310 (p : Pattern) (guard : d8111 p = 1) : d368 p ≤ (0 : Int) + d368 p := by
  omega
theorem compare38311 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d360 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38312 (p : Pattern) (guard : d8117 p = 1) : d468 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d468, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38310 p hg
    simpa only [d8117, d468, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d468, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38311 p hg
    simpa only [d8117, d468, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38313 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38314 (p : Pattern) (guard : d8123 p = 1) : d469 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d469, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38312 p hg
    simpa only [d8123, d469, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d469, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38313 p hg
    simpa only [d8123, d469, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38315 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38316 (p : Pattern) (guard : d8129 p = 1) : d470 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d470, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38314 p hg
    simpa only [d8129, d470, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d470, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38315 p hg
    simpa only [d8129, d470, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38317 (p : Pattern) (guard : d8135 p = 1) : d471 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d471, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38316 p hg
    simpa only [d8135, d471, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d471, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d471, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38318 (p : Pattern) (guard : d8136 p = 1) : d701 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d701, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35832 p hg
    simpa only [d8136, d701, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d701, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38317 p hg
    simpa only [d8136, d701, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38319 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38320 (p : Pattern) (guard : d8141 p = 1) : d702 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d702, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35850 p hg
    simpa only [d8141, d702, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d702, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38319 p hg
    simpa only [d8141, d702, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38321 (p : Pattern) (guard : d8142 p = 1) : d703 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d703, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38318 p hg
    simpa only [d8142, d703, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d703, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38320 p hg
    simpa only [d8142, d703, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38322 (p : Pattern) (guard : d0 p = 1) : d269 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38323 (p : Pattern) (guard : d8117 p = 1) : d291 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d291, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35797 p hg
    simpa only [d8117, d291, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d291, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38322 p hg
    simpa only [d8117, d291, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38324 (p : Pattern) (guard : d8123 p = 1) : d294 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d294, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38323 p hg
    simpa only [d8123, d294, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d294, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d8123, d294, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38325 (p : Pattern) (guard : d8129 p = 1) : d296 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d296, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38324 p hg
    simpa only [d8129, d296, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d296, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35848 p hg
    simpa only [d8129, d296, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38326 (p : Pattern) (guard : d8135 p = 1) : d297 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d297, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38325 p hg
    simpa only [d8135, d297, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d297, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4628 p hg
    simpa only [d8135, d297, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38327 (p : Pattern) (guard : d8141 p = 1) : d702 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d702, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38326 p hg
    simpa only [d8141, d702, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d702, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35859 p hg
    simpa only [d8141, d702, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38328 (p : Pattern) (guard : d8147 p = 1) : d704 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8141 p = 1 := by simpa only [d8147, d704, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38327 p hg
    simpa only [d8147, d704, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8147, d704, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8147, d704, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38329 (p : Pattern) (guard : d8148 p = 1) : d705 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d705, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38321 p hg
    simpa only [d8148, d705, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d705, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38328 p hg
    simpa only [d8148, d705, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38330 (p : Pattern) (guard : d8149 p = 1) : d706 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d706, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38309 p hg
    simpa only [d8149, d706, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d706, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38329 p hg
    simpa only [d8149, d706, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38331 (p : Pattern) (guard : d8150 p = 1) : d707 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d707, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38286 p hg
    simpa only [d8150, d707, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d707, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38330 p hg
    simpa only [d8150, d707, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38332 (p : Pattern) (guard : d8151 p = 1) : d708 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38259 p hg
    simpa only [d8151, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38331 p hg
    simpa only [d8151, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38333 (p : Pattern) (guard : d8152 p = 1) : d709 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38238 p hg
    simpa only [d8152, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38332 p hg
    simpa only [d8152, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38334 (p : Pattern) (guard : d1 p = 1) : d321 p ≤ (0 : Int) + d321 p := by
  omega
theorem compare38335 (p : Pattern) (guard : d1 p = 1) : d1682 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1682, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34323 p hg
    simpa only [d1682, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1682, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38334 p hg
    simpa only [d1682, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38336 (p : Pattern) (guard : d1 p = 1) : d1683 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38337 (p : Pattern) (guard : d1 p = 1) : d1684 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38336 p hg
    simpa only [d1684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d1684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38338 (p : Pattern) (guard : d1 p = 1) : d1685 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1685, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34321 p hg
    simpa only [d1685, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1685, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38337 p hg
    simpa only [d1685, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38339 (p : Pattern) (guard : d1 p = 1) : d1686 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1686, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38338 p hg
    simpa only [d1686, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1686, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38337 p hg
    simpa only [d1686, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38340 (p : Pattern) (guard : d8087 p = 1) : d1687 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d1687, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38339 p hg
    simpa only [d8087, d1687, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d1687, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34328 p hg
    simpa only [d8087, d1687, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38341 (p : Pattern) (guard : d8088 p = 1) : d1688 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8088, d1688, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38335 p hg
    simpa only [d8088, d1688, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8087 p = 1 := by simpa only [d8088, d1688, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38340 p hg
    simpa only [d8088, d1688, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38342 (p : Pattern) (guard : d8086 p = 1) : d333 p ≤ (0 : Int) + d333 p := by
  omega
theorem compare38343 (p : Pattern) (guard : d8087 p = 1) : d1689 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d1689, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34336 p hg
    simpa only [d8087, d1689, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d1689, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38342 p hg
    simpa only [d8087, d1689, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38344 (p : Pattern) (guard : d1 p = 1) : d1685 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1685, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34334 p hg
    simpa only [d1685, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1685, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38337 p hg
    simpa only [d1685, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38345 (p : Pattern) (guard : d8084 p = 1) : d1684 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d1684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38336 p hg
    simpa only [d8084, d1684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d1684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d8084, d1684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38346 (p : Pattern) (guard : d8085 p = 1) : d1684 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38337 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38345 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38347 (p : Pattern) (guard : d8086 p = 1) : d1686 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d1686, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38344 p hg
    simpa only [d8086, d1686, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d1686, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38346 p hg
    simpa only [d8086, d1686, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38348 (p : Pattern) (guard : d8091 p = 1) : d1687 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d1687, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38347 p hg
    simpa only [d8091, d1687, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d1687, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d1687, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38349 (p : Pattern) (guard : d8092 p = 1) : d1690 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d1690, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38343 p hg
    simpa only [d8092, d1690, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d1690, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38348 p hg
    simpa only [d8092, d1690, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38350 (p : Pattern) (guard : d8093 p = 1) : d1691 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8088 p = 1 := by simpa only [d8093, d1691, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38341 p hg
    simpa only [d8093, d1691, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8092 p = 1 := by simpa only [d8093, d1691, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38349 p hg
    simpa only [d8093, d1691, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38351 (p : Pattern) (guard : d8087 p = 1) : d15 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d15, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34350 p hg
    simpa only [d8087, d15, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d15, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34328 p hg
    simpa only [d8087, d15, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38352 (p : Pattern) (guard : d1 p = 1) : d1685 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1685, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34332 p hg
    simpa only [d1685, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1685, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38337 p hg
    simpa only [d1685, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38353 (p : Pattern) (guard : d8086 p = 1) : d1686 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d1686, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38352 p hg
    simpa only [d8086, d1686, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d1686, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38346 p hg
    simpa only [d8086, d1686, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38354 (p : Pattern) (guard : d8091 p = 1) : d1687 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d1687, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38353 p hg
    simpa only [d8091, d1687, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d1687, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d1687, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38355 (p : Pattern) (guard : d8092 p = 1) : d1692 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d1692, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38351 p hg
    simpa only [d8092, d1692, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d1692, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38354 p hg
    simpa only [d8092, d1692, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38356 (p : Pattern) (guard : d8091 p = 1) : d19 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d19, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34361 p hg
    simpa only [d8091, d19, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d19, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d19, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38357 (p : Pattern) (guard : d1 p = 1) : d1693 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare955 p hg
    simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38358 (p : Pattern) (guard : d8084 p = 1) : d1694 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38357 p hg
    simpa only [d8084, d1694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34420 p hg
    simpa only [d8084, d1694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38359 (p : Pattern) (guard : d8085 p = 1) : d1695 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d8085, d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38358 p hg
    simpa only [d8085, d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
