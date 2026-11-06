/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons242
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare34020 (p : Pattern) (guard : d8106 p = 1) : d0 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34019 p hg
    simpa only [d8106, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34012 p hg
    simpa only [d8106, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34021 (p : Pattern) (guard : d8107 p = 1) : d0 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33958 p hg
    simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34020 p hg
    simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34022 (p : Pattern) (guard : d8113 p = 1) : d0 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34021 p hg
    simpa only [d8113, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33937 p hg
    simpa only [d8113, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34023 (p : Pattern) (guard : d8114 p = 1) : d0 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34015 p hg
    simpa only [d8114, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34022 p hg
    simpa only [d8114, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34024 (p : Pattern) (guard : d8120 p = 1) : d0 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34023 p hg
    simpa only [d8120, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33972 p hg
    simpa only [d8120, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34025 (p : Pattern) (guard : d8121 p = 1) : d0 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33991 p hg
    simpa only [d8121, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34024 p hg
    simpa only [d8121, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34026 (p : Pattern) (guard : d8119 p = 1) : d0 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34022 p hg
    simpa only [d8119, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33944 p hg
    simpa only [d8119, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34027 (p : Pattern) (guard : d8125 p = 1) : d0 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34026 p hg
    simpa only [d8125, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33946 p hg
    simpa only [d8125, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34028 (p : Pattern) (guard : d8126 p = 1) : d0 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33940 p hg
    simpa only [d8126, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34027 p hg
    simpa only [d8126, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34029 (p : Pattern) (guard : d8127 p = 1) : d0 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34025 p hg
    simpa only [d8127, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34028 p hg
    simpa only [d8127, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34030 (p : Pattern) (guard : d8111 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34031 (p : Pattern) (guard : d8112 p = 1) : d0 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34020 p hg
    simpa only [d8112, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d8112, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34032 (p : Pattern) (guard : d8113 p = 1) : d0 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34014 p hg
    simpa only [d8113, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34031 p hg
    simpa only [d8113, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34033 (p : Pattern) (guard : d8119 p = 1) : d0 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34032 p hg
    simpa only [d8119, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33944 p hg
    simpa only [d8119, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34034 (p : Pattern) (guard : d8125 p = 1) : d0 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34033 p hg
    simpa only [d8125, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33946 p hg
    simpa only [d8125, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34035 (p : Pattern) (guard : d8126 p = 1) : d0 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33964 p hg
    simpa only [d8126, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34034 p hg
    simpa only [d8126, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34036 (p : Pattern) (guard : d8130 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34037 (p : Pattern) (guard : d8131 p = 1) : d0 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33968 p hg
    simpa only [d8131, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34036 p hg
    simpa only [d8131, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34038 (p : Pattern) (guard : d8132 p = 1) : d0 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34035 p hg
    simpa only [d8132, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34037 p hg
    simpa only [d8132, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34039 (p : Pattern) (guard : d8133 p = 1) : d0 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34029 p hg
    simpa only [d8133, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34038 p hg
    simpa only [d8133, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34040 (p : Pattern) (guard : d8102 p = 1) : d0 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33987 p hg
    simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34003 p hg
    simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34041 (p : Pattern) (guard : d8108 p = 1) : d0 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34040 p hg
    simpa only [d8108, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34021 p hg
    simpa only [d8108, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34042 (p : Pattern) (guard : d8114 p = 1) : d0 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34041 p hg
    simpa only [d8114, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33971 p hg
    simpa only [d8114, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34043 (p : Pattern) (guard : d8120 p = 1) : d0 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34042 p hg
    simpa only [d8120, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33967 p hg
    simpa only [d8120, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34044 (p : Pattern) (guard : d8084 p = 1) : d0 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33853 p hg
    simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34004 p hg
    simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34045 (p : Pattern) (guard : d8089 p = 1) : d0 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34044 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34006 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34046 (p : Pattern) (guard : d8094 p = 1) : d0 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34045 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34008 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34047 (p : Pattern) (guard : d8100 p = 1) : d0 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34046 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34048 (p : Pattern) (guard : d8106 p = 1) : d0 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34047 p hg
    simpa only [d8106, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34012 p hg
    simpa only [d8106, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34049 (p : Pattern) (guard : d8107 p = 1) : d0 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33998 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34048 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34050 (p : Pattern) (guard : d8112 p = 1) : d0 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34013 p hg
    simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d8112, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34051 (p : Pattern) (guard : d8113 p = 1) : d0 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34049 p hg
    simpa only [d8113, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34050 p hg
    simpa only [d8113, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34052 (p : Pattern) (guard : d8117 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34053 (p : Pattern) (guard : d8118 p = 1) : d0 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34031 p hg
    simpa only [d8118, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34052 p hg
    simpa only [d8118, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34054 (p : Pattern) (guard : d8119 p = 1) : d0 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34051 p hg
    simpa only [d8119, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34053 p hg
    simpa only [d8119, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34055 (p : Pattern) (guard : d8125 p = 1) : d0 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34054 p hg
    simpa only [d8125, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33946 p hg
    simpa only [d8125, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34056 (p : Pattern) (guard : d8126 p = 1) : d0 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34043 p hg
    simpa only [d8126, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34055 p hg
    simpa only [d8126, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34057 (p : Pattern) (guard : d8123 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34058 (p : Pattern) (guard : d8124 p = 1) : d0 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34053 p hg
    simpa only [d8124, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34057 p hg
    simpa only [d8124, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34059 (p : Pattern) (guard : d8129 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34060 (p : Pattern) (guard : d8130 p = 1) : d0 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34058 p hg
    simpa only [d8130, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34059 p hg
    simpa only [d8130, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34061 (p : Pattern) (guard : d8131 p = 1) : d0 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33973 p hg
    simpa only [d8131, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34060 p hg
    simpa only [d8131, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34062 (p : Pattern) (guard : d8132 p = 1) : d0 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34056 p hg
    simpa only [d8132, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34061 p hg
    simpa only [d8132, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34063 (p : Pattern) (guard : d8118 p = 1) : d0 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34050 p hg
    simpa only [d8118, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34052 p hg
    simpa only [d8118, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34064 (p : Pattern) (guard : d8124 p = 1) : d0 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34063 p hg
    simpa only [d8124, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34057 p hg
    simpa only [d8124, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34065 (p : Pattern) (guard : d8130 p = 1) : d0 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34064 p hg
    simpa only [d8130, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34059 p hg
    simpa only [d8130, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34066 (p : Pattern) (guard : d8131 p = 1) : d0 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34027 p hg
    simpa only [d8131, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34065 p hg
    simpa only [d8131, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34067 (p : Pattern) (guard : d8136 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34068 (p : Pattern) (guard : d8137 p = 1) : d0 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34066 p hg
    simpa only [d8137, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34067 p hg
    simpa only [d8137, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34069 (p : Pattern) (guard : d8138 p = 1) : d0 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34062 p hg
    simpa only [d8138, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34068 p hg
    simpa only [d8138, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34070 (p : Pattern) (guard : d8139 p = 1) : d0 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34039 p hg
    simpa only [d8139, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34069 p hg
    simpa only [d8139, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34071 (p : Pattern) (guard : d8140 p = 1) : d0 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33978 p hg
    simpa only [d8140, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34070 p hg
    simpa only [d8140, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34072 (p : Pattern) (guard : d8087 p = 1) : d0 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33802 p hg
    simpa only [d8087, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33849 p hg
    simpa only [d8087, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34073 (p : Pattern) (guard : d8092 p = 1) : d0 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34072 p hg
    simpa only [d8092, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33837 p hg
    simpa only [d8092, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34074 (p : Pattern) (guard : d8097 p = 1) : d0 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34073 p hg
    simpa only [d8097, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33994 p hg
    simpa only [d8097, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34075 (p : Pattern) (guard : d8103 p = 1) : d0 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34074 p hg
    simpa only [d8103, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34040 p hg
    simpa only [d8103, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34076 (p : Pattern) (guard : d8109 p = 1) : d0 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34075 p hg
    simpa only [d8109, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33961 p hg
    simpa only [d8109, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34077 (p : Pattern) (guard : d8115 p = 1) : d0 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34076 p hg
    simpa only [d8115, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33939 p hg
    simpa only [d8115, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34078 (p : Pattern) (guard : d8086 p = 1) : d0 p ≤ (0 : Int) + d381 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33881 p hg
    simpa only [d8086, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33893 p hg
    simpa only [d8086, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34079 (p : Pattern) (guard : d8091 p = 1) : d0 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34078 p hg
    simpa only [d8091, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33903 p hg
    simpa only [d8091, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34080 (p : Pattern) (guard : d8096 p = 1) : d0 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34079 p hg
    simpa only [d8096, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33897 p hg
    simpa only [d8096, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34081 (p : Pattern) (guard : d8085 p = 1) : d0 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33843 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33892 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34082 (p : Pattern) (guard : d8090 p = 1) : d0 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34081 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33894 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34083 (p : Pattern) (guard : d8095 p = 1) : d0 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34082 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33896 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34084 (p : Pattern) (guard : d8101 p = 1) : d0 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34083 p hg
    simpa only [d8101, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33898 p hg
    simpa only [d8101, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34085 (p : Pattern) (guard : d8102 p = 1) : d0 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34080 p hg
    simpa only [d8102, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34084 p hg
    simpa only [d8102, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34086 (p : Pattern) (guard : d8108 p = 1) : d0 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34085 p hg
    simpa only [d8108, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34049 p hg
    simpa only [d8108, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34087 (p : Pattern) (guard : d8114 p = 1) : d0 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34086 p hg
    simpa only [d8114, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34032 p hg
    simpa only [d8114, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34088 (p : Pattern) (guard : d8120 p = 1) : d0 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34087 p hg
    simpa only [d8120, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34026 p hg
    simpa only [d8120, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34089 (p : Pattern) (guard : d8121 p = 1) : d0 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34077 p hg
    simpa only [d8121, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34088 p hg
    simpa only [d8121, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34090 (p : Pattern) (guard : d8127 p = 1) : d0 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34089 p hg
    simpa only [d8127, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34035 p hg
    simpa only [d8127, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34091 (p : Pattern) (guard : d8133 p = 1) : d0 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34090 p hg
    simpa only [d8133, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34062 p hg
    simpa only [d8133, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34092 (p : Pattern) (guard : d8084 p = 1) : d0 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33795 p hg
    simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34004 p hg
    simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34093 (p : Pattern) (guard : d8089 p = 1) : d0 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34092 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34006 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34094 (p : Pattern) (guard : d8094 p = 1) : d0 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34093 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34008 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34095 (p : Pattern) (guard : d8100 p = 1) : d0 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34094 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34096 (p : Pattern) (guard : d8106 p = 1) : d0 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34095 p hg
    simpa only [d8106, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34012 p hg
    simpa only [d8106, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34097 (p : Pattern) (guard : d8107 p = 1) : d0 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34084 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34096 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34098 (p : Pattern) (guard : d8112 p = 1) : d0 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34048 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34099 (p : Pattern) (guard : d8113 p = 1) : d0 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34097 p hg
    simpa only [d8113, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34098 p hg
    simpa only [d8113, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34100 (p : Pattern) (guard : d8119 p = 1) : d0 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34099 p hg
    simpa only [d8119, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34063 p hg
    simpa only [d8119, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34101 (p : Pattern) (guard : d8125 p = 1) : d0 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34100 p hg
    simpa only [d8125, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34058 p hg
    simpa only [d8125, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34102 (p : Pattern) (guard : d8126 p = 1) : d0 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34024 p hg
    simpa only [d8126, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34101 p hg
    simpa only [d8126, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34103 (p : Pattern) (guard : d8132 p = 1) : d0 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34102 p hg
    simpa only [d8132, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34066 p hg
    simpa only [d8132, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34104 (p : Pattern) (guard : d8118 p = 1) : d0 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34098 p hg
    simpa only [d8118, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34052 p hg
    simpa only [d8118, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34105 (p : Pattern) (guard : d8124 p = 1) : d0 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34104 p hg
    simpa only [d8124, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34057 p hg
    simpa only [d8124, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34106 (p : Pattern) (guard : d8130 p = 1) : d0 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34105 p hg
    simpa only [d8130, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34059 p hg
    simpa only [d8130, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34107 (p : Pattern) (guard : d8131 p = 1) : d0 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34034 p hg
    simpa only [d8131, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34106 p hg
    simpa only [d8131, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34108 (p : Pattern) (guard : d8137 p = 1) : d0 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34107 p hg
    simpa only [d8137, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34067 p hg
    simpa only [d8137, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34109 (p : Pattern) (guard : d8138 p = 1) : d0 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34103 p hg
    simpa only [d8138, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34108 p hg
    simpa only [d8138, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34110 (p : Pattern) (guard : d8139 p = 1) : d0 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34091 p hg
    simpa only [d8139, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34109 p hg
    simpa only [d8139, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34111 (p : Pattern) (guard : d8086 p = 1) : d0 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33981 p hg
    simpa only [d8086, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33955 p hg
    simpa only [d8086, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34112 (p : Pattern) (guard : d8091 p = 1) : d0 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34111 p hg
    simpa only [d8091, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33895 p hg
    simpa only [d8091, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34113 (p : Pattern) (guard : d8096 p = 1) : d0 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34112 p hg
    simpa only [d8096, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33957 p hg
    simpa only [d8096, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34114 (p : Pattern) (guard : d8085 p = 1) : d0 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33830 p hg
    simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33892 p hg
    simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34115 (p : Pattern) (guard : d8090 p = 1) : d0 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34114 p hg
    simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34017 p hg
    simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34116 (p : Pattern) (guard : d8095 p = 1) : d0 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34115 p hg
    simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33896 p hg
    simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34117 (p : Pattern) (guard : d8101 p = 1) : d0 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34116 p hg
    simpa only [d8101, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34019 p hg
    simpa only [d8101, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34118 (p : Pattern) (guard : d8102 p = 1) : d0 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34113 p hg
    simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34117 p hg
    simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34119 (p : Pattern) (guard : d8108 p = 1) : d0 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34118 p hg
    simpa only [d8108, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34097 p hg
    simpa only [d8108, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34120 (p : Pattern) (guard : d8114 p = 1) : d0 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34119 p hg
    simpa only [d8114, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34051 p hg
    simpa only [d8114, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34121 (p : Pattern) (guard : d8120 p = 1) : d0 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34120 p hg
    simpa only [d8120, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34033 p hg
    simpa only [d8120, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34122 (p : Pattern) (guard : d8085 p = 1) : d0 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33812 p hg
    simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34123 (p : Pattern) (guard : d8090 p = 1) : d0 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34122 p hg
    simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34007 p hg
    simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34124 (p : Pattern) (guard : d8095 p = 1) : d0 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34123 p hg
    simpa only [d8095, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34018 p hg
    simpa only [d8095, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34125 (p : Pattern) (guard : d8101 p = 1) : d0 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34124 p hg
    simpa only [d8101, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d8101, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34126 (p : Pattern) (guard : d8084 p = 1) : d0 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33863 p hg
    simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34004 p hg
    simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34127 (p : Pattern) (guard : d8089 p = 1) : d0 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34126 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34006 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34128 (p : Pattern) (guard : d8094 p = 1) : d0 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34127 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34008 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34129 (p : Pattern) (guard : d8100 p = 1) : d0 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34128 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34130 (p : Pattern) (guard : d8106 p = 1) : d0 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34129 p hg
    simpa only [d8106, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34012 p hg
    simpa only [d8106, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34131 (p : Pattern) (guard : d8107 p = 1) : d0 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34125 p hg
    simpa only [d8107, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34130 p hg
    simpa only [d8107, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34132 (p : Pattern) (guard : d8084 p = 1) : d0 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33799 p hg
    simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34004 p hg
    simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34133 (p : Pattern) (guard : d8089 p = 1) : d0 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34132 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34006 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34134 (p : Pattern) (guard : d8094 p = 1) : d0 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34133 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34008 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34135 (p : Pattern) (guard : d8100 p = 1) : d0 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34134 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34136 (p : Pattern) (guard : d8106 p = 1) : d0 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34135 p hg
    simpa only [d8106, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34012 p hg
    simpa only [d8106, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34137 (p : Pattern) (guard : d5843 p = 1) : d0 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33815 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34138 (p : Pattern) (guard : d5847 p = 1) : d0 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34137 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34139 (p : Pattern) (guard : d5854 p = 1) : d0 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34138 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34140 (p : Pattern) (guard : d8099 p = 1) : d0 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34139 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34141 (p : Pattern) (guard : d8105 p = 1) : d0 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34140 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34142 (p : Pattern) (guard : d8111 p = 1) : d0 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34141 p hg
    simpa only [d8111, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8111, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34143 (p : Pattern) (guard : d8112 p = 1) : d0 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34136 p hg
    simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34142 p hg
    simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34144 (p : Pattern) (guard : d8113 p = 1) : d0 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34131 p hg
    simpa only [d8113, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34143 p hg
    simpa only [d8113, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34145 (p : Pattern) (guard : d5843 p = 1) : d0 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1492 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34146 (p : Pattern) (guard : d5847 p = 1) : d0 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34145 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34147 (p : Pattern) (guard : d5854 p = 1) : d0 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34146 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34148 (p : Pattern) (guard : d8099 p = 1) : d0 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34147 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34149 (p : Pattern) (guard : d8105 p = 1) : d0 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34148 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34150 (p : Pattern) (guard : d8111 p = 1) : d0 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34149 p hg
    simpa only [d8111, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d8111, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34151 (p : Pattern) (guard : d8112 p = 1) : d0 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34096 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34150 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34152 (p : Pattern) (guard : d8118 p = 1) : d0 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34151 p hg
    simpa only [d8118, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34052 p hg
    simpa only [d8118, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34153 (p : Pattern) (guard : d8119 p = 1) : d0 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34144 p hg
    simpa only [d8119, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34152 p hg
    simpa only [d8119, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34154 (p : Pattern) (guard : d8125 p = 1) : d0 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34153 p hg
    simpa only [d8125, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34105 p hg
    simpa only [d8125, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34155 (p : Pattern) (guard : d8126 p = 1) : d0 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34121 p hg
    simpa only [d8126, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34154 p hg
    simpa only [d8126, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34156 (p : Pattern) (guard : d8124 p = 1) : d0 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34152 p hg
    simpa only [d8124, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34057 p hg
    simpa only [d8124, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34157 (p : Pattern) (guard : d8130 p = 1) : d0 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34156 p hg
    simpa only [d8130, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34059 p hg
    simpa only [d8130, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34158 (p : Pattern) (guard : d8131 p = 1) : d0 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34055 p hg
    simpa only [d8131, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34157 p hg
    simpa only [d8131, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34159 (p : Pattern) (guard : d8132 p = 1) : d0 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34155 p hg
    simpa only [d8132, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34158 p hg
    simpa only [d8132, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
