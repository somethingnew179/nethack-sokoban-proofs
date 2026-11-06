/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons328
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare46060 (p : Pattern) (guard : d8121 p = 1) : d734 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d734, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46057 p hg
    simpa only [d8121, d734, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d734, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46059 p hg
    simpa only [d8121, d734, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46061 (p : Pattern) (guard : d8120 p = 1) : d726 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d726, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34825 p hg
    simpa only [d8120, d726, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d726, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46029 p hg
    simpa only [d8120, d726, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46062 (p : Pattern) (guard : d8125 p = 1) : d714 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d714, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34838 p hg
    simpa only [d8125, d714, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d714, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d714, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46063 (p : Pattern) (guard : d8126 p = 1) : d727 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d727, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46061 p hg
    simpa only [d8126, d727, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d727, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46062 p hg
    simpa only [d8126, d727, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46064 (p : Pattern) (guard : d8127 p = 1) : d735 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d735, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46060 p hg
    simpa only [d8127, d735, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d735, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46063 p hg
    simpa only [d8127, d735, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46065 (p : Pattern) (guard : d8120 p = 1) : d713 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d713, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35009 p hg
    simpa only [d8120, d713, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d713, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46043 p hg
    simpa only [d8120, d713, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46066 (p : Pattern) (guard : d8125 p = 1) : d714 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d714, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35023 p hg
    simpa only [d8125, d714, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d714, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d714, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46067 (p : Pattern) (guard : d8126 p = 1) : d715 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d715, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46065 p hg
    simpa only [d8126, d715, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d715, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46066 p hg
    simpa only [d8126, d715, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46068 (p : Pattern) (guard : d8125 p = 1) : d719 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d719, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38151 p hg
    simpa only [d8125, d719, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d719, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d719, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46069 (p : Pattern) (guard : d8131 p = 1) : d720 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d720, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46068 p hg
    simpa only [d8131, d720, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d720, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41400 p hg
    simpa only [d8131, d720, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46070 (p : Pattern) (guard : d8132 p = 1) : d736 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d736, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46067 p hg
    simpa only [d8132, d736, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d736, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46069 p hg
    simpa only [d8132, d736, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46071 (p : Pattern) (guard : d8133 p = 1) : d737 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d737, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46064 p hg
    simpa only [d8133, d737, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d737, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46070 p hg
    simpa only [d8133, d737, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46072 (p : Pattern) (guard : d8119 p = 1) : d405 p ≤ (0 : Int) + d405 p := by
  omega
theorem compare46073 (p : Pattern) (guard : d8120 p = 1) : d717 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d717, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34858 p hg
    simpa only [d8120, d717, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d717, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46072 p hg
    simpa only [d8120, d717, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46074 (p : Pattern) (guard : d8125 p = 1) : d714 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d714, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34895 p hg
    simpa only [d8125, d714, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d714, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d714, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46075 (p : Pattern) (guard : d8126 p = 1) : d718 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d718, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46073 p hg
    simpa only [d8126, d718, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d718, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46074 p hg
    simpa only [d8126, d718, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46076 (p : Pattern) (guard : d8125 p = 1) : d726 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d726, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d8125, d726, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d726, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d726, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46077 (p : Pattern) (guard : d8130 p = 1) : d714 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d714, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34935 p hg
    simpa only [d8130, d714, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d714, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d714, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46078 (p : Pattern) (guard : d8131 p = 1) : d727 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d727, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46076 p hg
    simpa only [d8131, d727, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d727, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46077 p hg
    simpa only [d8131, d727, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46079 (p : Pattern) (guard : d8132 p = 1) : d738 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d738, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46075 p hg
    simpa only [d8132, d738, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d738, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46078 p hg
    simpa only [d8132, d738, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46080 (p : Pattern) (guard : d8125 p = 1) : d726 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d726, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35067 p hg
    simpa only [d8125, d726, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d726, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d726, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46081 (p : Pattern) (guard : d8130 p = 1) : d714 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d714, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35076 p hg
    simpa only [d8130, d714, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d714, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d714, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46082 (p : Pattern) (guard : d8131 p = 1) : d727 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d727, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46080 p hg
    simpa only [d8131, d727, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d727, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46081 p hg
    simpa only [d8131, d727, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46083 (p : Pattern) (guard : d8137 p = 1) : d729 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d729, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46082 p hg
    simpa only [d8137, d729, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d729, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d729, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46084 (p : Pattern) (guard : d8138 p = 1) : d739 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d739, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46079 p hg
    simpa only [d8138, d739, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d739, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46083 p hg
    simpa only [d8138, d739, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46085 (p : Pattern) (guard : d8139 p = 1) : d740 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d740, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46071 p hg
    simpa only [d8139, d740, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d740, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46084 p hg
    simpa only [d8139, d740, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46086 (p : Pattern) (guard : d8140 p = 1) : d741 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d741, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46055 p hg
    simpa only [d8140, d741, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d741, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46085 p hg
    simpa only [d8140, d741, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46087 (p : Pattern) (guard : d8114 p = 1) : d376 p ≤ (0 : Int) + d376 p := by
  omega
theorem compare46088 (p : Pattern) (guard : d8115 p = 1) : d710 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d710, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34954 p hg
    simpa only [d8115, d710, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d710, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46087 p hg
    simpa only [d8115, d710, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46089 (p : Pattern) (guard : d8119 p = 1) : d391 p ≤ (0 : Int) + d391 p := by
  omega
theorem compare46090 (p : Pattern) (guard : d8120 p = 1) : d711 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d711, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d8120, d711, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d711, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46089 p hg
    simpa only [d8120, d711, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46091 (p : Pattern) (guard : d8121 p = 1) : d712 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d712, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46088 p hg
    simpa only [d8121, d712, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d712, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46090 p hg
    simpa only [d8121, d712, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46092 (p : Pattern) (guard : d8127 p = 1) : d716 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d716, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46091 p hg
    simpa only [d8127, d716, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d716, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46067 p hg
    simpa only [d8127, d716, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46093 (p : Pattern) (guard : d8125 p = 1) : d719 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d719, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38179 p hg
    simpa only [d8125, d719, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d719, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d719, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46094 (p : Pattern) (guard : d8131 p = 1) : d720 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d720, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46093 p hg
    simpa only [d8131, d720, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d720, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41412 p hg
    simpa only [d8131, d720, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46095 (p : Pattern) (guard : d8132 p = 1) : d721 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d721, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46075 p hg
    simpa only [d8132, d721, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d721, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46094 p hg
    simpa only [d8132, d721, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46096 (p : Pattern) (guard : d8133 p = 1) : d722 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d722, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46092 p hg
    simpa only [d8133, d722, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d722, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46095 p hg
    simpa only [d8133, d722, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46097 (p : Pattern) (guard : d8120 p = 1) : d723 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d723, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35033 p hg
    simpa only [d8120, d723, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d723, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46058 p hg
    simpa only [d8120, d723, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46098 (p : Pattern) (guard : d8124 p = 1) : d396 p ≤ (0 : Int) + d396 p := by
  omega
theorem compare46099 (p : Pattern) (guard : d8125 p = 1) : d724 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d724, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35058 p hg
    simpa only [d8125, d724, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d724, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46098 p hg
    simpa only [d8125, d724, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46100 (p : Pattern) (guard : d8126 p = 1) : d725 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d725, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46097 p hg
    simpa only [d8126, d725, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d725, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46099 p hg
    simpa only [d8126, d725, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46101 (p : Pattern) (guard : d8132 p = 1) : d728 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d728, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46100 p hg
    simpa only [d8132, d728, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d728, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46082 p hg
    simpa only [d8132, d728, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46102 (p : Pattern) (guard : d8125 p = 1) : d726 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d726, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38189 p hg
    simpa only [d8125, d726, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d726, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d726, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46103 (p : Pattern) (guard : d8130 p = 1) : d714 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d714, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41418 p hg
    simpa only [d8130, d714, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d714, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d714, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46104 (p : Pattern) (guard : d8131 p = 1) : d727 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d727, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46102 p hg
    simpa only [d8131, d727, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d727, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46103 p hg
    simpa only [d8131, d727, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46105 (p : Pattern) (guard : d8137 p = 1) : d729 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d729, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46104 p hg
    simpa only [d8137, d729, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d729, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d729, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46106 (p : Pattern) (guard : d8138 p = 1) : d730 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d730, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46101 p hg
    simpa only [d8138, d730, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d730, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46105 p hg
    simpa only [d8138, d730, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46107 (p : Pattern) (guard : d8139 p = 1) : d731 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d731, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46096 p hg
    simpa only [d8139, d731, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d731, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46106 p hg
    simpa only [d8139, d731, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46108 (p : Pattern) (guard : d8119 p = 1) : d398 p ≤ (0 : Int) + d398 p := by
  omega
theorem compare46109 (p : Pattern) (guard : d8120 p = 1) : d742 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d742, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35159 p hg
    simpa only [d8120, d742, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d742, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46108 p hg
    simpa only [d8120, d742, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46110 (p : Pattern) (guard : d8124 p = 1) : d409 p ≤ (0 : Int) + d409 p := by
  omega
theorem compare46111 (p : Pattern) (guard : d8125 p = 1) : d743 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d743, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35235 p hg
    simpa only [d8125, d743, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d743, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46110 p hg
    simpa only [d8125, d743, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46112 (p : Pattern) (guard : d8126 p = 1) : d744 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d744, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46109 p hg
    simpa only [d8126, d744, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d744, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46111 p hg
    simpa only [d8126, d744, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46113 (p : Pattern) (guard : d8125 p = 1) : d745 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d745, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35263 p hg
    simpa only [d8125, d745, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d745, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d745, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46114 (p : Pattern) (guard : d8130 p = 1) : d746 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d746, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35289 p hg
    simpa only [d8130, d746, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d746, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d746, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46115 (p : Pattern) (guard : d8131 p = 1) : d747 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d747, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46113 p hg
    simpa only [d8131, d747, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d747, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46114 p hg
    simpa only [d8131, d747, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46116 (p : Pattern) (guard : d8132 p = 1) : d748 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d748, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46112 p hg
    simpa only [d8132, d748, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d748, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46115 p hg
    simpa only [d8132, d748, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46117 (p : Pattern) (guard : d8125 p = 1) : d749 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d749, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38204 p hg
    simpa only [d8125, d749, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d749, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46098 p hg
    simpa only [d8125, d749, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46118 (p : Pattern) (guard : d8130 p = 1) : d746 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d746, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41429 p hg
    simpa only [d8130, d746, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d746, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d746, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46119 (p : Pattern) (guard : d8131 p = 1) : d750 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d750, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46117 p hg
    simpa only [d8131, d750, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d750, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46118 p hg
    simpa only [d8131, d750, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46120 (p : Pattern) (guard : d8137 p = 1) : d751 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d751, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46119 p hg
    simpa only [d8137, d751, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d751, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38220 p hg
    simpa only [d8137, d751, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46121 (p : Pattern) (guard : d8138 p = 1) : d752 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d752, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46116 p hg
    simpa only [d8138, d752, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d752, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46120 p hg
    simpa only [d8138, d752, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46122 (p : Pattern) (guard : d8124 p = 1) : d405 p ≤ (0 : Int) + d405 p := by
  omega
theorem compare46123 (p : Pattern) (guard : d8125 p = 1) : d753 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d753, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35314 p hg
    simpa only [d8125, d753, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d753, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46122 p hg
    simpa only [d8125, d753, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46124 (p : Pattern) (guard : d8130 p = 1) : d746 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d746, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35347 p hg
    simpa only [d8130, d746, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d746, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d746, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46125 (p : Pattern) (guard : d8131 p = 1) : d754 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d754, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46123 p hg
    simpa only [d8131, d754, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d754, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46124 p hg
    simpa only [d8131, d754, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46126 (p : Pattern) (guard : d8130 p = 1) : d745 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d745, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35359 p hg
    simpa only [d8130, d745, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d745, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d745, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46127 (p : Pattern) (guard : d8135 p = 1) : d746 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d746, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35373 p hg
    simpa only [d8135, d746, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d746, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d746, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46128 (p : Pattern) (guard : d8136 p = 1) : d747 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d747, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46126 p hg
    simpa only [d8136, d747, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d747, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46127 p hg
    simpa only [d8136, d747, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46129 (p : Pattern) (guard : d8137 p = 1) : d755 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d755, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46125 p hg
    simpa only [d8137, d755, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d755, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46128 p hg
    simpa only [d8137, d755, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46130 (p : Pattern) (guard : d8130 p = 1) : d745 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d745, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38230 p hg
    simpa only [d8130, d745, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d745, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d745, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46131 (p : Pattern) (guard : d8135 p = 1) : d746 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d746, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41436 p hg
    simpa only [d8135, d746, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d746, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d746, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46132 (p : Pattern) (guard : d8136 p = 1) : d747 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d747, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46130 p hg
    simpa only [d8136, d747, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d747, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46131 p hg
    simpa only [d8136, d747, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46133 (p : Pattern) (guard : d8142 p = 1) : d756 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d756, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46132 p hg
    simpa only [d8142, d756, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d756, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d756, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46134 (p : Pattern) (guard : d8143 p = 1) : d757 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d757, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46129 p hg
    simpa only [d8143, d757, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d757, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46133 p hg
    simpa only [d8143, d757, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46135 (p : Pattern) (guard : d8144 p = 1) : d758 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d758, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46121 p hg
    simpa only [d8144, d758, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d758, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46134 p hg
    simpa only [d8144, d758, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46136 (p : Pattern) (guard : d8145 p = 1) : d759 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d759, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46107 p hg
    simpa only [d8145, d759, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d759, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46135 p hg
    simpa only [d8145, d759, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46137 (p : Pattern) (guard : d8146 p = 1) : d760 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46086 p hg
    simpa only [d8146, d760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46136 p hg
    simpa only [d8146, d760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46138 (p : Pattern) (guard : d8120 p = 1) : d732 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d732, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35402 p hg
    simpa only [d8120, d732, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d732, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46108 p hg
    simpa only [d8120, d732, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46139 (p : Pattern) (guard : d8125 p = 1) : d733 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d733, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35443 p hg
    simpa only [d8125, d733, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d733, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46110 p hg
    simpa only [d8125, d733, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46140 (p : Pattern) (guard : d8126 p = 1) : d734 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d734, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46138 p hg
    simpa only [d8126, d734, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d734, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46139 p hg
    simpa only [d8126, d734, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46141 (p : Pattern) (guard : d8125 p = 1) : d726 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d726, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35460 p hg
    simpa only [d8125, d726, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d726, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d726, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46142 (p : Pattern) (guard : d8130 p = 1) : d714 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d714, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35475 p hg
    simpa only [d8130, d714, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d714, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d714, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46143 (p : Pattern) (guard : d8131 p = 1) : d727 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d727, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46141 p hg
    simpa only [d8131, d727, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d727, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46142 p hg
    simpa only [d8131, d727, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46144 (p : Pattern) (guard : d8132 p = 1) : d735 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d735, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46140 p hg
    simpa only [d8132, d735, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d735, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46143 p hg
    simpa only [d8132, d735, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46145 (p : Pattern) (guard : d8125 p = 1) : d713 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d713, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35619 p hg
    simpa only [d8125, d713, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d713, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46098 p hg
    simpa only [d8125, d713, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46146 (p : Pattern) (guard : d8130 p = 1) : d714 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d714, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35633 p hg
    simpa only [d8130, d714, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d714, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d714, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46147 (p : Pattern) (guard : d8131 p = 1) : d715 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d715, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46145 p hg
    simpa only [d8131, d715, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d715, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46146 p hg
    simpa only [d8131, d715, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46148 (p : Pattern) (guard : d8130 p = 1) : d719 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d719, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38246 p hg
    simpa only [d8130, d719, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d719, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d719, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46149 (p : Pattern) (guard : d8136 p = 1) : d720 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d720, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46148 p hg
    simpa only [d8136, d720, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d720, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41444 p hg
    simpa only [d8136, d720, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46150 (p : Pattern) (guard : d8137 p = 1) : d736 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d736, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46147 p hg
    simpa only [d8137, d736, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d736, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46149 p hg
    simpa only [d8137, d736, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46151 (p : Pattern) (guard : d8138 p = 1) : d737 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d737, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46144 p hg
    simpa only [d8138, d737, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d737, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46150 p hg
    simpa only [d8138, d737, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46152 (p : Pattern) (guard : d8125 p = 1) : d717 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d717, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35496 p hg
    simpa only [d8125, d717, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d717, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46122 p hg
    simpa only [d8125, d717, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46153 (p : Pattern) (guard : d8130 p = 1) : d714 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d714, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35531 p hg
    simpa only [d8130, d714, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d714, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d714, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46154 (p : Pattern) (guard : d8131 p = 1) : d718 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d718, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46152 p hg
    simpa only [d8131, d718, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d718, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46153 p hg
    simpa only [d8131, d718, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46155 (p : Pattern) (guard : d8130 p = 1) : d761 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d761, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d8130, d761, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d761, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d761, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46156 (p : Pattern) (guard : d8135 p = 1) : d762 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d762, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41472 p hg
    simpa only [d8135, d762, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d762, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d762, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46157 (p : Pattern) (guard : d8136 p = 1) : d763 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d763, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46155 p hg
    simpa only [d8136, d763, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d763, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46156 p hg
    simpa only [d8136, d763, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46158 (p : Pattern) (guard : d8137 p = 1) : d764 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d764, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46154 p hg
    simpa only [d8137, d764, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d764, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46157 p hg
    simpa only [d8137, d764, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46159 (p : Pattern) (guard : d8130 p = 1) : d761 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d761, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41477 p hg
    simpa only [d8130, d761, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d761, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d761, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46160 (p : Pattern) (guard : d8135 p = 1) : d762 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d762, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41481 p hg
    simpa only [d8135, d762, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d762, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d762, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46161 (p : Pattern) (guard : d8136 p = 1) : d763 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d763, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46159 p hg
    simpa only [d8136, d763, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d763, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46160 p hg
    simpa only [d8136, d763, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46162 (p : Pattern) (guard : d8142 p = 1) : d765 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d765, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46161 p hg
    simpa only [d8142, d765, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d765, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d765, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46163 (p : Pattern) (guard : d8143 p = 1) : d766 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d766, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46158 p hg
    simpa only [d8143, d766, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d766, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46162 p hg
    simpa only [d8143, d766, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46164 (p : Pattern) (guard : d8144 p = 1) : d767 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d767, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46151 p hg
    simpa only [d8144, d767, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d767, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46163 p hg
    simpa only [d8144, d767, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46165 (p : Pattern) (guard : d8145 p = 1) : d768 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d768, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46107 p hg
    simpa only [d8145, d768, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d768, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46164 p hg
    simpa only [d8145, d768, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46166 (p : Pattern) (guard : d8119 p = 1) : d376 p ≤ (0 : Int) + d376 p := by
  omega
theorem compare46167 (p : Pattern) (guard : d8120 p = 1) : d710 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d710, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35572 p hg
    simpa only [d8120, d710, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d710, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46166 p hg
    simpa only [d8120, d710, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46168 (p : Pattern) (guard : d8124 p = 1) : d391 p ≤ (0 : Int) + d391 p := by
  omega
theorem compare46169 (p : Pattern) (guard : d8125 p = 1) : d711 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d711, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35608 p hg
    simpa only [d8125, d711, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d711, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46168 p hg
    simpa only [d8125, d711, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46170 (p : Pattern) (guard : d8126 p = 1) : d712 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d712, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46167 p hg
    simpa only [d8126, d712, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d712, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46169 p hg
    simpa only [d8126, d712, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46171 (p : Pattern) (guard : d8132 p = 1) : d716 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d716, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46170 p hg
    simpa only [d8132, d716, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d716, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46147 p hg
    simpa only [d8132, d716, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46172 (p : Pattern) (guard : d8130 p = 1) : d719 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d719, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38270 p hg
    simpa only [d8130, d719, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d719, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d719, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46173 (p : Pattern) (guard : d8136 p = 1) : d720 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d720, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46172 p hg
    simpa only [d8136, d720, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d720, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41492 p hg
    simpa only [d8136, d720, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46174 (p : Pattern) (guard : d8137 p = 1) : d721 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d721, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46154 p hg
    simpa only [d8137, d721, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d721, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46173 p hg
    simpa only [d8137, d721, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46175 (p : Pattern) (guard : d8138 p = 1) : d722 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d722, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46171 p hg
    simpa only [d8138, d722, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d722, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46174 p hg
    simpa only [d8138, d722, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46176 (p : Pattern) (guard : d8125 p = 1) : d723 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d723, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35643 p hg
    simpa only [d8125, d723, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d723, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46110 p hg
    simpa only [d8125, d723, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46177 (p : Pattern) (guard : d8129 p = 1) : d396 p ≤ (0 : Int) + d396 p := by
  omega
theorem compare46178 (p : Pattern) (guard : d8130 p = 1) : d724 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d724, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35671 p hg
    simpa only [d8130, d724, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d724, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46177 p hg
    simpa only [d8130, d724, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46179 (p : Pattern) (guard : d8131 p = 1) : d725 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d725, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46176 p hg
    simpa only [d8131, d725, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d725, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46178 p hg
    simpa only [d8131, d725, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46180 (p : Pattern) (guard : d8130 p = 1) : d726 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d726, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35680 p hg
    simpa only [d8130, d726, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d726, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d726, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46181 (p : Pattern) (guard : d8135 p = 1) : d714 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d714, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35689 p hg
    simpa only [d8135, d714, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d714, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d714, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46182 (p : Pattern) (guard : d8136 p = 1) : d727 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d727, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46180 p hg
    simpa only [d8136, d727, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d727, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46181 p hg
    simpa only [d8136, d727, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46183 (p : Pattern) (guard : d8137 p = 1) : d728 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d728, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46179 p hg
    simpa only [d8137, d728, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d728, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46182 p hg
    simpa only [d8137, d728, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46184 (p : Pattern) (guard : d8130 p = 1) : d726 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d726, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38280 p hg
    simpa only [d8130, d726, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d726, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d726, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46185 (p : Pattern) (guard : d8135 p = 1) : d714 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d714, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41500 p hg
    simpa only [d8135, d714, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d714, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d714, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46186 (p : Pattern) (guard : d8136 p = 1) : d727 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d727, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46184 p hg
    simpa only [d8136, d727, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d727, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46185 p hg
    simpa only [d8136, d727, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46187 (p : Pattern) (guard : d8142 p = 1) : d729 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d729, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46186 p hg
    simpa only [d8142, d729, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d729, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d729, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46188 (p : Pattern) (guard : d8143 p = 1) : d730 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d730, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46183 p hg
    simpa only [d8143, d730, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d730, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46187 p hg
    simpa only [d8143, d730, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46189 (p : Pattern) (guard : d8144 p = 1) : d731 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d731, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46175 p hg
    simpa only [d8144, d731, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d731, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46188 p hg
    simpa only [d8144, d731, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46190 (p : Pattern) (guard : d8124 p = 1) : d398 p ≤ (0 : Int) + d398 p := by
  omega
theorem compare46191 (p : Pattern) (guard : d8125 p = 1) : d742 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d742, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35730 p hg
    simpa only [d8125, d742, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d742, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46190 p hg
    simpa only [d8125, d742, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46192 (p : Pattern) (guard : d8130 p = 1) : d769 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d769, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35770 p hg
    simpa only [d8130, d769, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d769, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38290 p hg
    simpa only [d8130, d769, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46193 (p : Pattern) (guard : d8131 p = 1) : d770 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d770, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46191 p hg
    simpa only [d8131, d770, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d770, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46192 p hg
    simpa only [d8131, d770, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46194 (p : Pattern) (guard : d8130 p = 1) : d745 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d745, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35790 p hg
    simpa only [d8130, d745, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d745, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d745, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46195 (p : Pattern) (guard : d8135 p = 1) : d771 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d771, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35800 p hg
    simpa only [d8135, d771, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d771, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d771, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46196 (p : Pattern) (guard : d8136 p = 1) : d772 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d772, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46194 p hg
    simpa only [d8136, d772, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d772, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46195 p hg
    simpa only [d8136, d772, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46197 (p : Pattern) (guard : d8137 p = 1) : d773 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d773, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46193 p hg
    simpa only [d8137, d773, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d773, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46196 p hg
    simpa only [d8137, d773, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46198 (p : Pattern) (guard : d8130 p = 1) : d749 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d749, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38298 p hg
    simpa only [d8130, d749, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d749, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46177 p hg
    simpa only [d8130, d749, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46199 (p : Pattern) (guard : d8135 p = 1) : d771 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d771, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41509 p hg
    simpa only [d8135, d771, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d771, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d771, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
