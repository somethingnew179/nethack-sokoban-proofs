/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons318
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare44660 (p : Pattern) (guard : d8109 p = 1) : d3327 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d3327, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44658 p hg
    simpa only [d8109, d3327, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d3327, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44659 p hg
    simpa only [d8109, d3327, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44661 (p : Pattern) (guard : d8096 p = 1) : d3252 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3252, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44432 p hg
    simpa only [d8096, d3252, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3252, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44481 p hg
    simpa only [d8096, d3252, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44662 (p : Pattern) (guard : d5854 p = 1) : d3226 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44429 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26609 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44663 (p : Pattern) (guard : d8094 p = 1) : d3226 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44430 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44662 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44664 (p : Pattern) (guard : d8095 p = 1) : d3226 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44431 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44663 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44665 (p : Pattern) (guard : d8101 p = 1) : d3255 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44664 p hg
    simpa only [d8101, d3255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44568 p hg
    simpa only [d8101, d3255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44666 (p : Pattern) (guard : d8102 p = 1) : d3256 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3256, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44661 p hg
    simpa only [d8102, d3256, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3256, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44665 p hg
    simpa only [d8102, d3256, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44667 (p : Pattern) (guard : d8101 p = 1) : d3259 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44664 p hg
    simpa only [d8101, d3259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44514 p hg
    simpa only [d8101, d3259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44668 (p : Pattern) (guard : d8099 p = 1) : d3239 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44451 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26627 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44669 (p : Pattern) (guard : d8100 p = 1) : d3239 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44452 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44668 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44670 (p : Pattern) (guard : d8106 p = 1) : d3260 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44669 p hg
    simpa only [d8106, d3260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44671 (p : Pattern) (guard : d8107 p = 1) : d3261 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44667 p hg
    simpa only [d8107, d3261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44670 p hg
    simpa only [d8107, d3261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44672 (p : Pattern) (guard : d8108 p = 1) : d3262 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3262, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44666 p hg
    simpa only [d8108, d3262, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3262, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44671 p hg
    simpa only [d8108, d3262, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44673 (p : Pattern) (guard : d8101 p = 1) : d3263 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44664 p hg
    simpa only [d8101, d3263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d3263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44674 (p : Pattern) (guard : d8107 p = 1) : d3264 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44673 p hg
    simpa only [d8107, d3264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44670 p hg
    simpa only [d8107, d3264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44675 (p : Pattern) (guard : d8112 p = 1) : d3266 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44532 p hg
    simpa only [d8112, d3266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44676 (p : Pattern) (guard : d8113 p = 1) : d3267 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44674 p hg
    simpa only [d8113, d3267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44675 p hg
    simpa only [d8113, d3267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44677 (p : Pattern) (guard : d8114 p = 1) : d3268 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3268, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44672 p hg
    simpa only [d8114, d3268, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3268, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44676 p hg
    simpa only [d8114, d3268, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44678 (p : Pattern) (guard : d8115 p = 1) : d3328 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d3328, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44660 p hg
    simpa only [d8115, d3328, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d3328, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44677 p hg
    simpa only [d8115, d3328, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44679 (p : Pattern) (guard : d8086 p = 1) : d3226 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44390 p hg
    simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44361 p hg
    simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44680 (p : Pattern) (guard : d8091 p = 1) : d3226 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44679 p hg
    simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44431 p hg
    simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44681 (p : Pattern) (guard : d8096 p = 1) : d3238 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3238, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44680 p hg
    simpa only [d8096, d3238, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3238, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44547 p hg
    simpa only [d8096, d3238, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44682 (p : Pattern) (guard : d1 p = 1) : d3250 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3250, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34656 p hg
    simpa only [d3250, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3250, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3250, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44683 (p : Pattern) (guard : d8085 p = 1) : d3250 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44682 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44421 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44684 (p : Pattern) (guard : d8090 p = 1) : d3250 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44683 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44478 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44685 (p : Pattern) (guard : d8095 p = 1) : d3250 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44684 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44526 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44686 (p : Pattern) (guard : d8101 p = 1) : d3275 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3275, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44685 p hg
    simpa only [d8101, d3275, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3275, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44584 p hg
    simpa only [d8101, d3275, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44687 (p : Pattern) (guard : d8102 p = 1) : d3306 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3306, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44681 p hg
    simpa only [d8102, d3306, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3306, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44686 p hg
    simpa only [d8102, d3306, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44688 (p : Pattern) (guard : d1 p = 1) : d3239 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3239, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34663 p hg
    simpa only [d3239, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3239, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3239, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44689 (p : Pattern) (guard : d8085 p = 1) : d3239 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44688 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44378 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44690 (p : Pattern) (guard : d8090 p = 1) : d3239 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44689 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44382 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44691 (p : Pattern) (guard : d8095 p = 1) : d3239 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44690 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44452 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44692 (p : Pattern) (guard : d8101 p = 1) : d3241 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3241, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44691 p hg
    simpa only [d8101, d3241, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3241, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44551 p hg
    simpa only [d8101, d3241, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44693 (p : Pattern) (guard : d8107 p = 1) : d3277 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3277, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44692 p hg
    simpa only [d8107, d3277, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3277, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44593 p hg
    simpa only [d8107, d3277, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44694 (p : Pattern) (guard : d8108 p = 1) : d3307 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3307, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44687 p hg
    simpa only [d8108, d3307, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3307, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44693 p hg
    simpa only [d8108, d3307, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44695 (p : Pattern) (guard : d8107 p = 1) : d3282 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3282, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44636 p hg
    simpa only [d8107, d3282, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3282, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44597 p hg
    simpa only [d8107, d3282, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44696 (p : Pattern) (guard : d8113 p = 1) : d3285 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3285, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44695 p hg
    simpa only [d8113, d3285, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3285, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44601 p hg
    simpa only [d8113, d3285, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44697 (p : Pattern) (guard : d8114 p = 1) : d3308 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3308, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44694 p hg
    simpa only [d8114, d3308, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3308, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44696 p hg
    simpa only [d8114, d3308, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44698 (p : Pattern) (guard : d8085 p = 1) : d3226 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44354 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44360 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44699 (p : Pattern) (guard : d8090 p = 1) : d3226 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44698 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44430 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44700 (p : Pattern) (guard : d8095 p = 1) : d3226 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44699 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44663 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44701 (p : Pattern) (guard : d8101 p = 1) : d3255 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3255, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44700 p hg
    simpa only [d8101, d3255, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3255, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44568 p hg
    simpa only [d8101, d3255, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44702 (p : Pattern) (guard : d8099 p = 1) : d3250 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44525 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26644 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44703 (p : Pattern) (guard : d8100 p = 1) : d3250 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44526 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44702 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44704 (p : Pattern) (guard : d8106 p = 1) : d3287 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44703 p hg
    simpa only [d8106, d3287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44705 (p : Pattern) (guard : d8107 p = 1) : d3288 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3288, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44701 p hg
    simpa only [d8107, d3288, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3288, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44704 p hg
    simpa only [d8107, d3288, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44706 (p : Pattern) (guard : d8105 p = 1) : d3244 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44530 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26636 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44707 (p : Pattern) (guard : d8111 p = 1) : d3265 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44706 p hg
    simpa only [d8111, d3265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44708 (p : Pattern) (guard : d8112 p = 1) : d3289 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44670 p hg
    simpa only [d8112, d3289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44707 p hg
    simpa only [d8112, d3289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44709 (p : Pattern) (guard : d8113 p = 1) : d3290 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3290, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44705 p hg
    simpa only [d8113, d3290, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3290, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44708 p hg
    simpa only [d8113, d3290, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44710 (p : Pattern) (guard : d8105 p = 1) : d3279 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44535 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26681 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44711 (p : Pattern) (guard : d8111 p = 1) : d3291 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44710 p hg
    simpa only [d8111, d3291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44712 (p : Pattern) (guard : d8112 p = 1) : d3292 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44670 p hg
    simpa only [d8112, d3292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44711 p hg
    simpa only [d8112, d3292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44713 (p : Pattern) (guard : d8105 p = 1) : d3257 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44539 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26655 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44714 (p : Pattern) (guard : d8111 p = 1) : d3293 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44713 p hg
    simpa only [d8111, d3293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44715 (p : Pattern) (guard : d8117 p = 1) : d3294 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44714 p hg
    simpa only [d8117, d3294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44716 (p : Pattern) (guard : d8118 p = 1) : d3295 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44712 p hg
    simpa only [d8118, d3295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44715 p hg
    simpa only [d8118, d3295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44717 (p : Pattern) (guard : d8119 p = 1) : d3296 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3296, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44709 p hg
    simpa only [d8119, d3296, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3296, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44716 p hg
    simpa only [d8119, d3296, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44718 (p : Pattern) (guard : d8120 p = 1) : d3329 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3329, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44697 p hg
    simpa only [d8120, d3329, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3329, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44717 p hg
    simpa only [d8120, d3329, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44719 (p : Pattern) (guard : d8121 p = 1) : d3330 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d3330, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44678 p hg
    simpa only [d8121, d3330, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d3330, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44718 p hg
    simpa only [d8121, d3330, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44720 (p : Pattern) (guard : d8100 p = 1) : d3230 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44663 p hg
    simpa only [d8100, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44721 (p : Pattern) (guard : d8101 p = 1) : d3238 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3238, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44700 p hg
    simpa only [d8101, d3238, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3238, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44720 p hg
    simpa only [d8101, d3238, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44722 (p : Pattern) (guard : d8102 p = 1) : d3238 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44548 p hg
    simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44721 p hg
    simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44723 (p : Pattern) (guard : d8101 p = 1) : d3238 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44664 p hg
    simpa only [d8101, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44720 p hg
    simpa only [d8101, d3238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44724 (p : Pattern) (guard : d8105 p = 1) : d3240 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44668 p hg
    simpa only [d8105, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44725 (p : Pattern) (guard : d8106 p = 1) : d3241 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44669 p hg
    simpa only [d8106, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44724 p hg
    simpa only [d8106, d3241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44726 (p : Pattern) (guard : d8107 p = 1) : d3242 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44723 p hg
    simpa only [d8107, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44725 p hg
    simpa only [d8107, d3242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44727 (p : Pattern) (guard : d8108 p = 1) : d3299 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3299, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44722 p hg
    simpa only [d8108, d3299, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3299, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44726 p hg
    simpa only [d8108, d3299, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44728 (p : Pattern) (guard : d8112 p = 1) : d3247 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44593 p hg
    simpa only [d8112, d3247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44729 (p : Pattern) (guard : d8113 p = 1) : d3248 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44726 p hg
    simpa only [d8113, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44728 p hg
    simpa only [d8113, d3248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44730 (p : Pattern) (guard : d8114 p = 1) : d3300 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3300, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44727 p hg
    simpa only [d8114, d3300, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3300, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44729 p hg
    simpa only [d8114, d3300, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44731 (p : Pattern) (guard : d8095 p = 1) : d3250 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44479 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44526 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44732 (p : Pattern) (guard : d8101 p = 1) : d3275 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44731 p hg
    simpa only [d8101, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44584 p hg
    simpa only [d8101, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44733 (p : Pattern) (guard : d8099 p = 1) : d3253 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44565 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26649 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44734 (p : Pattern) (guard : d8100 p = 1) : d3253 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44566 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44733 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44735 (p : Pattern) (guard : d8105 p = 1) : d3254 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44733 p hg
    simpa only [d8105, d3254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44736 (p : Pattern) (guard : d8106 p = 1) : d3301 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44734 p hg
    simpa only [d8106, d3301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44735 p hg
    simpa only [d8106, d3301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44737 (p : Pattern) (guard : d8107 p = 1) : d3302 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44732 p hg
    simpa only [d8107, d3302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44736 p hg
    simpa only [d8107, d3302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44738 (p : Pattern) (guard : d8113 p = 1) : d3303 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44737 p hg
    simpa only [d8113, d3303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44601 p hg
    simpa only [d8113, d3303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44739 (p : Pattern) (guard : d8119 p = 1) : d3304 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44738 p hg
    simpa only [d8119, d3304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d3304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44740 (p : Pattern) (guard : d8120 p = 1) : d3305 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3305, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44730 p hg
    simpa only [d8120, d3305, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3305, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44739 p hg
    simpa only [d8120, d3305, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44741 (p : Pattern) (guard : d8085 p = 1) : d3226 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44356 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44360 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44742 (p : Pattern) (guard : d8090 p = 1) : d3226 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44741 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44430 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44743 (p : Pattern) (guard : d8095 p = 1) : d3226 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44742 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44663 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44744 (p : Pattern) (guard : d8101 p = 1) : d3238 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3238, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44743 p hg
    simpa only [d8101, d3238, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3238, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44720 p hg
    simpa only [d8101, d3238, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44745 (p : Pattern) (guard : d8105 p = 1) : d3251 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44702 p hg
    simpa only [d8105, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44746 (p : Pattern) (guard : d8106 p = 1) : d3275 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44703 p hg
    simpa only [d8106, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44745 p hg
    simpa only [d8106, d3275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44747 (p : Pattern) (guard : d8107 p = 1) : d3306 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3306, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44744 p hg
    simpa only [d8107, d3306, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3306, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44746 p hg
    simpa only [d8107, d3306, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44748 (p : Pattern) (guard : d0 p = 1) : d3245 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44749 (p : Pattern) (guard : d8111 p = 1) : d3246 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44706 p hg
    simpa only [d8111, d3246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44748 p hg
    simpa only [d8111, d3246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44750 (p : Pattern) (guard : d8112 p = 1) : d3277 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44725 p hg
    simpa only [d8112, d3277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44749 p hg
    simpa only [d8112, d3277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44751 (p : Pattern) (guard : d8113 p = 1) : d3307 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3307, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44747 p hg
    simpa only [d8113, d3307, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3307, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44750 p hg
    simpa only [d8113, d3307, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44752 (p : Pattern) (guard : d0 p = 1) : d3280 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44753 (p : Pattern) (guard : d8111 p = 1) : d3281 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44710 p hg
    simpa only [d8111, d3281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44752 p hg
    simpa only [d8111, d3281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44754 (p : Pattern) (guard : d8112 p = 1) : d3282 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44725 p hg
    simpa only [d8112, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44753 p hg
    simpa only [d8112, d3282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44755 (p : Pattern) (guard : d0 p = 1) : d3258 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44756 (p : Pattern) (guard : d8111 p = 1) : d3283 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44713 p hg
    simpa only [d8111, d3283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44755 p hg
    simpa only [d8111, d3283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44757 (p : Pattern) (guard : d8117 p = 1) : d3284 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44756 p hg
    simpa only [d8117, d3284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44758 (p : Pattern) (guard : d8118 p = 1) : d3285 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44754 p hg
    simpa only [d8118, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44757 p hg
    simpa only [d8118, d3285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44759 (p : Pattern) (guard : d8119 p = 1) : d3308 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3308, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44751 p hg
    simpa only [d8119, d3308, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3308, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44758 p hg
    simpa only [d8119, d3308, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44760 (p : Pattern) (guard : d8112 p = 1) : d3309 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44736 p hg
    simpa only [d8112, d3309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44761 (p : Pattern) (guard : d8118 p = 1) : d3310 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44760 p hg
    simpa only [d8118, d3310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d3310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44762 (p : Pattern) (guard : d8124 p = 1) : d3311 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44761 p hg
    simpa only [d8124, d3311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44763 (p : Pattern) (guard : d8125 p = 1) : d3312 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3312, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44759 p hg
    simpa only [d8125, d3312, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3312, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44762 p hg
    simpa only [d8125, d3312, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44764 (p : Pattern) (guard : d8126 p = 1) : d3313 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3313, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44740 p hg
    simpa only [d8126, d3313, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3313, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44763 p hg
    simpa only [d8126, d3313, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44765 (p : Pattern) (guard : d8127 p = 1) : d3331 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d3331, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44719 p hg
    simpa only [d8127, d3331, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d3331, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44764 p hg
    simpa only [d8127, d3331, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44766 (p : Pattern) (guard : d8102 p = 1) : d3238 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44579 p hg
    simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44744 p hg
    simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44767 (p : Pattern) (guard : d8107 p = 1) : d3242 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3242, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44721 p hg
    simpa only [d8107, d3242, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3242, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44725 p hg
    simpa only [d8107, d3242, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44768 (p : Pattern) (guard : d8108 p = 1) : d3299 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3299, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44766 p hg
    simpa only [d8108, d3299, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3299, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44767 p hg
    simpa only [d8108, d3299, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44769 (p : Pattern) (guard : d8114 p = 1) : d3300 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3300, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44768 p hg
    simpa only [d8114, d3300, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3300, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44729 p hg
    simpa only [d8114, d3300, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44770 (p : Pattern) (guard : d8120 p = 1) : d3305 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3305, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44769 p hg
    simpa only [d8120, d3305, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3305, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44739 p hg
    simpa only [d8120, d3305, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44771 (p : Pattern) (guard : d8085 p = 1) : d3226 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44426 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44360 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44772 (p : Pattern) (guard : d8090 p = 1) : d3226 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44771 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44430 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44773 (p : Pattern) (guard : d8095 p = 1) : d3226 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44772 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44663 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44774 (p : Pattern) (guard : d8101 p = 1) : d3238 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3238, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44773 p hg
    simpa only [d8101, d3238, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3238, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44720 p hg
    simpa only [d8101, d3238, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44775 (p : Pattern) (guard : d8107 p = 1) : d3306 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3306, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44774 p hg
    simpa only [d8107, d3306, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3306, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44746 p hg
    simpa only [d8107, d3306, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44776 (p : Pattern) (guard : d8113 p = 1) : d3307 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3307, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44775 p hg
    simpa only [d8113, d3307, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3307, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44750 p hg
    simpa only [d8113, d3307, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44777 (p : Pattern) (guard : d8119 p = 1) : d3308 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3308, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44776 p hg
    simpa only [d8119, d3308, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3308, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44758 p hg
    simpa only [d8119, d3308, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44778 (p : Pattern) (guard : d8125 p = 1) : d3312 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3312, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44777 p hg
    simpa only [d8125, d3312, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3312, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44762 p hg
    simpa only [d8125, d3312, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44779 (p : Pattern) (guard : d8126 p = 1) : d3313 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3313, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44770 p hg
    simpa only [d8126, d3313, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3313, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44778 p hg
    simpa only [d8126, d3313, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44780 (p : Pattern) (guard : d8132 p = 1) : d3332 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d3332, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44779 p hg
    simpa only [d8132, d3332, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d3332, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d8132, d3332, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44781 (p : Pattern) (guard : d8133 p = 1) : d3333 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d3333, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44765 p hg
    simpa only [d8133, d3333, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d3333, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44780 p hg
    simpa only [d8133, d3333, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44782 (p : Pattern) (guard : d8134 p = 1) : d3334 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8128 p = 1 := by simpa only [d8134, d3334, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44655 p hg
    simpa only [d8134, d3334, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8133 p = 1 := by simpa only [d8134, d3334, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44781 p hg
    simpa only [d8134, d3334, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44783 (p : Pattern) (guard : d1 p = 1) : d3335 p ≤ (0 : Int) + d429 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3335, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33979 p hg
    simpa only [d3335, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3335, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35948 p hg
    simpa only [d3335, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44784 (p : Pattern) (guard : d1 p = 1) : d3336 p ≤ (0 : Int) + d430 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3336, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44783 p hg
    simpa only [d3336, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3336, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44426 p hg
    simpa only [d3336, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44785 (p : Pattern) (guard : d1 p = 1) : d3337 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3337, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44784 p hg
    simpa only [d3337, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3337, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44347 p hg
    simpa only [d3337, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44786 (p : Pattern) (guard : d8087 p = 1) : d3338 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d3338, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44785 p hg
    simpa only [d8087, d3338, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d3338, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44428 p hg
    simpa only [d8087, d3338, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44787 (p : Pattern) (guard : d8091 p = 1) : d3230 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3230, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44519 p hg
    simpa only [d8091, d3230, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3230, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d3230, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44788 (p : Pattern) (guard : d8092 p = 1) : d3339 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d3339, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44786 p hg
    simpa only [d8092, d3339, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d3339, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44787 p hg
    simpa only [d8092, d3339, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44789 (p : Pattern) (guard : d8086 p = 1) : d3226 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44369 p hg
    simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44698 p hg
    simpa only [d8086, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44790 (p : Pattern) (guard : d8091 p = 1) : d3226 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44789 p hg
    simpa only [d8091, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44431 p hg
    simpa only [d8091, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44791 (p : Pattern) (guard : d8095 p = 1) : d3230 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3230, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44699 p hg
    simpa only [d8095, d3230, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3230, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3230, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44792 (p : Pattern) (guard : d8096 p = 1) : d3238 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3238, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44790 p hg
    simpa only [d8096, d3238, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3238, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44791 p hg
    simpa only [d8096, d3238, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44793 (p : Pattern) (guard : d8097 p = 1) : d3340 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d3340, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44788 p hg
    simpa only [d8097, d3340, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d3340, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44792 p hg
    simpa only [d8097, d3340, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44794 (p : Pattern) (guard : d8085 p = 1) : d3239 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44395 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44378 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44795 (p : Pattern) (guard : d8090 p = 1) : d3239 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44794 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44382 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44796 (p : Pattern) (guard : d8095 p = 1) : d3239 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44795 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44452 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44797 (p : Pattern) (guard : d8101 p = 1) : d3241 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3241, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44796 p hg
    simpa only [d8101, d3241, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3241, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44551 p hg
    simpa only [d8101, d3241, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44798 (p : Pattern) (guard : d8102 p = 1) : d3242 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3242, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44681 p hg
    simpa only [d8102, d3242, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3242, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44797 p hg
    simpa only [d8102, d3242, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44799 (p : Pattern) (guard : d8103 p = 1) : d3341 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d3341, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44793 p hg
    simpa only [d8103, d3341, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d3341, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44798 p hg
    simpa only [d8103, d3341, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
