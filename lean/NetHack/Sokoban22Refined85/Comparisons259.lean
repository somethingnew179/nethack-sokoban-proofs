/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons258
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare36260 (p : Pattern) (guard : d8086 p = 1) : d30 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36259 p hg
    simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36057 p hg
    simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36261 (p : Pattern) (guard : d8091 p = 1) : d3643 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3643, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36260 p hg
    simpa only [d8091, d3643, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3643, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36191 p hg
    simpa only [d8091, d3643, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36262 (p : Pattern) (guard : d8096 p = 1) : d3678 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3678, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36261 p hg
    simpa only [d8096, d3678, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3678, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36193 p hg
    simpa only [d8096, d3678, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36263 (p : Pattern) (guard : d8102 p = 1) : d3681 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3681, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36262 p hg
    simpa only [d8102, d3681, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3681, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36206 p hg
    simpa only [d8102, d3681, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36264 (p : Pattern) (guard : d8108 p = 1) : d3682 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3682, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36263 p hg
    simpa only [d8108, d3682, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3682, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36212 p hg
    simpa only [d8108, d3682, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36265 (p : Pattern) (guard : d8114 p = 1) : d3683 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3683, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36264 p hg
    simpa only [d8114, d3683, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3683, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d3683, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36266 (p : Pattern) (guard : d8115 p = 1) : d3684 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d3684, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36258 p hg
    simpa only [d8115, d3684, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d3684, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36265 p hg
    simpa only [d8115, d3684, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36267 (p : Pattern) (guard : d8086 p = 1) : d13 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35971 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35990 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36268 (p : Pattern) (guard : d8091 p = 1) : d3582 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3582, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36267 p hg
    simpa only [d8091, d3582, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3582, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35996 p hg
    simpa only [d8091, d3582, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36269 (p : Pattern) (guard : d8096 p = 1) : d3665 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3665, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36268 p hg
    simpa only [d8096, d3665, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3665, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36169 p hg
    simpa only [d8096, d3665, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36270 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10844 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36271 (p : Pattern) (guard : d8085 p = 1) : d30 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36270 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36056 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36272 (p : Pattern) (guard : d8090 p = 1) : d30 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36271 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36126 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36273 (p : Pattern) (guard : d8095 p = 1) : d3643 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3643, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36272 p hg
    simpa only [d8095, d3643, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3643, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36131 p hg
    simpa only [d8095, d3643, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36274 (p : Pattern) (guard : d8101 p = 1) : d3678 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3678, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36273 p hg
    simpa only [d8101, d3678, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3678, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36224 p hg
    simpa only [d8101, d3678, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36275 (p : Pattern) (guard : d8102 p = 1) : d3685 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3685, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36269 p hg
    simpa only [d8102, d3685, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3685, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36274 p hg
    simpa only [d8102, d3685, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36276 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1200 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36277 (p : Pattern) (guard : d8085 p = 1) : d17 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36276 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35914 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36278 (p : Pattern) (guard : d8090 p = 1) : d17 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36277 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36017 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36279 (p : Pattern) (guard : d8095 p = 1) : d3605 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3605, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36278 p hg
    simpa only [d8095, d3605, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3605, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36022 p hg
    simpa only [d8095, d3605, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36280 (p : Pattern) (guard : d8101 p = 1) : d3670 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3670, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36279 p hg
    simpa only [d8101, d3670, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3670, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36174 p hg
    simpa only [d8101, d3670, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36281 (p : Pattern) (guard : d8107 p = 1) : d3686 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3686, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36280 p hg
    simpa only [d8107, d3686, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3686, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36233 p hg
    simpa only [d8107, d3686, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36282 (p : Pattern) (guard : d8108 p = 1) : d3687 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3687, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36275 p hg
    simpa only [d8108, d3687, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3687, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36281 p hg
    simpa only [d8108, d3687, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36283 (p : Pattern) (guard : d8107 p = 1) : d3688 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3688, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36231 p hg
    simpa only [d8107, d3688, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3688, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36237 p hg
    simpa only [d8107, d3688, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36284 (p : Pattern) (guard : d8113 p = 1) : d3689 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3689, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36283 p hg
    simpa only [d8113, d3689, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3689, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36241 p hg
    simpa only [d8113, d3689, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36285 (p : Pattern) (guard : d8114 p = 1) : d3690 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3690, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36282 p hg
    simpa only [d8114, d3690, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3690, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36284 p hg
    simpa only [d8114, d3690, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36286 (p : Pattern) (guard : d8120 p = 1) : d3694 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3694, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36285 p hg
    simpa only [d8120, d3694, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3694, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36246 p hg
    simpa only [d8120, d3694, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36287 (p : Pattern) (guard : d8121 p = 1) : d3695 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d3695, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36266 p hg
    simpa only [d8121, d3695, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d3695, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36286 p hg
    simpa only [d8121, d3695, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36288 (p : Pattern) (guard : d8095 p = 1) : d3673 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35958 p hg
    simpa only [d8095, d3673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36289 (p : Pattern) (guard : d8096 p = 1) : d3674 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3674, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35959 p hg
    simpa only [d8096, d3674, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3674, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36288 p hg
    simpa only [d8096, d3674, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36290 (p : Pattern) (guard : d8102 p = 1) : d3697 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3697, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36289 p hg
    simpa only [d8102, d3697, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3697, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36211 p hg
    simpa only [d8102, d3697, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36291 (p : Pattern) (guard : d8108 p = 1) : d3698 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3698, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36290 p hg
    simpa only [d8108, d3698, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3698, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36212 p hg
    simpa only [d8108, d3698, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36292 (p : Pattern) (guard : d8113 p = 1) : d3699 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36212 p hg
    simpa only [d8113, d3699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d3699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36293 (p : Pattern) (guard : d8114 p = 1) : d3700 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3700, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36291 p hg
    simpa only [d8114, d3700, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3700, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36292 p hg
    simpa only [d8114, d3700, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36294 (p : Pattern) (guard : d8119 p = 1) : d3701 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36292 p hg
    simpa only [d8119, d3701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d3701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36295 (p : Pattern) (guard : d8120 p = 1) : d3702 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3702, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36293 p hg
    simpa only [d8120, d3702, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3702, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36294 p hg
    simpa only [d8120, d3702, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36296 (p : Pattern) (guard : d8113 p = 1) : d3699 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3699, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36116 p hg
    simpa only [d8113, d3699, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3699, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d3699, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36297 (p : Pattern) (guard : d8119 p = 1) : d3701 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3701, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36296 p hg
    simpa only [d8119, d3701, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3701, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d3701, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36298 (p : Pattern) (guard : d8124 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare36299 (p : Pattern) (guard : d8125 p = 1) : d3703 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3703, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36297 p hg
    simpa only [d8125, d3703, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3703, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36298 p hg
    simpa only [d8125, d3703, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36300 (p : Pattern) (guard : d8126 p = 1) : d3704 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3704, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36295 p hg
    simpa only [d8126, d3704, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3704, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36299 p hg
    simpa only [d8126, d3704, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36301 (p : Pattern) (guard : d8127 p = 1) : d3705 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d3705, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36287 p hg
    simpa only [d8127, d3705, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d3705, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36300 p hg
    simpa only [d8127, d3705, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36302 (p : Pattern) (guard : d8128 p = 1) : d3706 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8122 p = 1 := by simpa only [d8128, d3706, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36249 p hg
    simpa only [d8128, d3706, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8127 p = 1 := by simpa only [d8128, d3706, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36301 p hg
    simpa only [d8128, d3706, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36303 (p : Pattern) (guard : d8085 p = 1) : d3544 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d8085, d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35890 p hg
    simpa only [d8085, d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36304 (p : Pattern) (guard : d5847 p = 1) : d3543 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d5847, d3543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5847, d3543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36305 (p : Pattern) (guard : d8089 p = 1) : d3543 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35890 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36304 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36306 (p : Pattern) (guard : d8090 p = 1) : d3545 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36303 p hg
    simpa only [d8090, d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36305 p hg
    simpa only [d8090, d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36307 (p : Pattern) (guard : d8091 p = 1) : d3552 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3552, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36267 p hg
    simpa only [d8091, d3552, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3552, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36306 p hg
    simpa only [d8091, d3552, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36308 (p : Pattern) (guard : d8085 p = 1) : d3548 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1499 p hg
    simpa only [d8085, d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35895 p hg
    simpa only [d8085, d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36309 (p : Pattern) (guard : d5847 p = 1) : d3547 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d5847, d3547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5847, d3547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36310 (p : Pattern) (guard : d8089 p = 1) : d3547 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35895 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36309 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36311 (p : Pattern) (guard : d8090 p = 1) : d3549 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36308 p hg
    simpa only [d8090, d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36310 p hg
    simpa only [d8090, d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36312 (p : Pattern) (guard : d8095 p = 1) : d3550 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36311 p hg
    simpa only [d8095, d3550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36313 (p : Pattern) (guard : d8096 p = 1) : d3553 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3553, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36307 p hg
    simpa only [d8096, d3553, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3553, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36312 p hg
    simpa only [d8096, d3553, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36314 (p : Pattern) (guard : d8097 p = 1) : d3553 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35899 p hg
    simpa only [d8097, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36313 p hg
    simpa only [d8097, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36315 (p : Pattern) (guard : d8091 p = 1) : d3552 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3552, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36216 p hg
    simpa only [d8091, d3552, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3552, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36306 p hg
    simpa only [d8091, d3552, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36316 (p : Pattern) (guard : d8096 p = 1) : d3553 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3553, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36315 p hg
    simpa only [d8096, d3553, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3553, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36312 p hg
    simpa only [d8096, d3553, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36317 (p : Pattern) (guard : d8089 p = 1) : d3556 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35914 p hg
    simpa only [d8089, d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35920 p hg
    simpa only [d8089, d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36318 (p : Pattern) (guard : d5854 p = 1) : d3555 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35920 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29237 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36319 (p : Pattern) (guard : d8094 p = 1) : d3557 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36317 p hg
    simpa only [d8094, d3557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36318 p hg
    simpa only [d8094, d3557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36320 (p : Pattern) (guard : d8095 p = 1) : d3558 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3558, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36278 p hg
    simpa only [d8095, d3558, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3558, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36319 p hg
    simpa only [d8095, d3558, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36321 (p : Pattern) (guard : d8089 p = 1) : d3560 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35914 p hg
    simpa only [d8089, d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35926 p hg
    simpa only [d8089, d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36322 (p : Pattern) (guard : d5854 p = 1) : d3559 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35926 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29244 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36323 (p : Pattern) (guard : d8094 p = 1) : d3561 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36321 p hg
    simpa only [d8094, d3561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36322 p hg
    simpa only [d8094, d3561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36324 (p : Pattern) (guard : d8100 p = 1) : d3562 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36323 p hg
    simpa only [d8100, d3562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36325 (p : Pattern) (guard : d8101 p = 1) : d3563 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3563, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36320 p hg
    simpa only [d8101, d3563, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3563, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36324 p hg
    simpa only [d8101, d3563, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36326 (p : Pattern) (guard : d8102 p = 1) : d3564 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3564, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36316 p hg
    simpa only [d8102, d3564, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3564, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36325 p hg
    simpa only [d8102, d3564, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36327 (p : Pattern) (guard : d8103 p = 1) : d3707 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d3707, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36314 p hg
    simpa only [d8103, d3707, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d3707, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36326 p hg
    simpa only [d8103, d3707, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36328 (p : Pattern) (guard : d8091 p = 1) : d3552 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3552, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36120 p hg
    simpa only [d8091, d3552, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3552, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36306 p hg
    simpa only [d8091, d3552, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36329 (p : Pattern) (guard : d8096 p = 1) : d3553 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3553, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36328 p hg
    simpa only [d8096, d3553, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3553, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36312 p hg
    simpa only [d8096, d3553, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36330 (p : Pattern) (guard : d8095 p = 1) : d3558 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3558, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36229 p hg
    simpa only [d8095, d3558, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3558, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36319 p hg
    simpa only [d8095, d3558, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36331 (p : Pattern) (guard : d8101 p = 1) : d3563 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3563, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36330 p hg
    simpa only [d8101, d3563, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3563, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36324 p hg
    simpa only [d8101, d3563, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36332 (p : Pattern) (guard : d8102 p = 1) : d3564 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3564, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36329 p hg
    simpa only [d8102, d3564, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3564, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36331 p hg
    simpa only [d8102, d3564, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36333 (p : Pattern) (guard : d8101 p = 1) : d3573 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36037 p hg
    simpa only [d8101, d3573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36084 p hg
    simpa only [d8101, d3573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36334 (p : Pattern) (guard : d8107 p = 1) : d3574 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36333 p hg
    simpa only [d8107, d3574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d3574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36335 (p : Pattern) (guard : d8108 p = 1) : d3575 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3575, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36332 p hg
    simpa only [d8108, d3575, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3575, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36334 p hg
    simpa only [d8108, d3575, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36336 (p : Pattern) (guard : d8109 p = 1) : d3708 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d3708, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36327 p hg
    simpa only [d8109, d3708, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d3708, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36335 p hg
    simpa only [d8109, d3708, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36337 (p : Pattern) (guard : d8096 p = 1) : d3589 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3589, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35997 p hg
    simpa only [d8096, d3589, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3589, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36193 p hg
    simpa only [d8096, d3589, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36338 (p : Pattern) (guard : d5847 p = 1) : d13 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d5847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36339 (p : Pattern) (guard : d8089 p = 1) : d13 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35989 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36338 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36340 (p : Pattern) (guard : d8090 p = 1) : d13 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35990 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36339 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36341 (p : Pattern) (guard : d5847 p = 1) : d3577 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d5847, d3577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d5847, d3577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36342 (p : Pattern) (guard : d8089 p = 1) : d3578 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35989 p hg
    simpa only [d8089, d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36341 p hg
    simpa only [d8089, d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36343 (p : Pattern) (guard : d5854 p = 1) : d3580 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36304 p hg
    simpa only [d5854, d3580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29273 p hg
    simpa only [d5854, d3580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36344 (p : Pattern) (guard : d8094 p = 1) : d3581 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36342 p hg
    simpa only [d8094, d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36343 p hg
    simpa only [d8094, d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36345 (p : Pattern) (guard : d8095 p = 1) : d3582 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36340 p hg
    simpa only [d8095, d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36344 p hg
    simpa only [d8095, d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36346 (p : Pattern) (guard : d8101 p = 1) : d3595 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36345 p hg
    simpa only [d8101, d3595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36205 p hg
    simpa only [d8101, d3595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36347 (p : Pattern) (guard : d8102 p = 1) : d3596 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3596, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36337 p hg
    simpa only [d8102, d3596, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3596, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36346 p hg
    simpa only [d8102, d3596, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36348 (p : Pattern) (guard : d8101 p = 1) : d3600 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36345 p hg
    simpa only [d8101, d3600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36114 p hg
    simpa only [d8101, d3600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36349 (p : Pattern) (guard : d5854 p = 1) : d17 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36016 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36350 (p : Pattern) (guard : d8094 p = 1) : d17 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36017 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36349 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36351 (p : Pattern) (guard : d5854 p = 1) : d3602 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36016 p hg
    simpa only [d5854, d3602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29301 p hg
    simpa only [d5854, d3602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36352 (p : Pattern) (guard : d8099 p = 1) : d3604 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36351 p hg
    simpa only [d8099, d3604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31580 p hg
    simpa only [d8099, d3604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36353 (p : Pattern) (guard : d8100 p = 1) : d3605 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36350 p hg
    simpa only [d8100, d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36352 p hg
    simpa only [d8100, d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36354 (p : Pattern) (guard : d8106 p = 1) : d3606 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36353 p hg
    simpa only [d8106, d3606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36355 (p : Pattern) (guard : d8107 p = 1) : d3607 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36348 p hg
    simpa only [d8107, d3607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36354 p hg
    simpa only [d8107, d3607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36356 (p : Pattern) (guard : d8108 p = 1) : d3608 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3608, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36347 p hg
    simpa only [d8108, d3608, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3608, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36355 p hg
    simpa only [d8108, d3608, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36357 (p : Pattern) (guard : d8101 p = 1) : d3609 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36345 p hg
    simpa only [d8101, d3609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d3609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36358 (p : Pattern) (guard : d8107 p = 1) : d3610 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36357 p hg
    simpa only [d8107, d3610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36354 p hg
    simpa only [d8107, d3610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36359 (p : Pattern) (guard : d8112 p = 1) : d3612 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36140 p hg
    simpa only [d8112, d3612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36360 (p : Pattern) (guard : d8113 p = 1) : d3613 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36358 p hg
    simpa only [d8113, d3613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36359 p hg
    simpa only [d8113, d3613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36361 (p : Pattern) (guard : d8114 p = 1) : d3614 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3614, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36356 p hg
    simpa only [d8114, d3614, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3614, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36360 p hg
    simpa only [d8114, d3614, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36362 (p : Pattern) (guard : d8115 p = 1) : d3709 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d3709, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36336 p hg
    simpa only [d8115, d3709, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d3709, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36361 p hg
    simpa only [d8115, d3709, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36363 (p : Pattern) (guard : d8086 p = 1) : d13 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35934 p hg
    simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35990 p hg
    simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36364 (p : Pattern) (guard : d8091 p = 1) : d3552 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3552, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36363 p hg
    simpa only [d8091, d3552, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3552, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36306 p hg
    simpa only [d8091, d3552, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36365 (p : Pattern) (guard : d8096 p = 1) : d3553 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3553, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36364 p hg
    simpa only [d8096, d3553, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3553, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36312 p hg
    simpa only [d8096, d3553, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36366 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4512 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36367 (p : Pattern) (guard : d8085 p = 1) : d30 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36366 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36056 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36368 (p : Pattern) (guard : d8090 p = 1) : d30 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36367 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36126 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36369 (p : Pattern) (guard : d8089 p = 1) : d3621 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36056 p hg
    simpa only [d8089, d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36061 p hg
    simpa only [d8089, d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36370 (p : Pattern) (guard : d5854 p = 1) : d3585 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36061 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29325 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36371 (p : Pattern) (guard : d8094 p = 1) : d3622 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36369 p hg
    simpa only [d8094, d3622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36370 p hg
    simpa only [d8094, d3622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36372 (p : Pattern) (guard : d8095 p = 1) : d3623 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3623, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36368 p hg
    simpa only [d8095, d3623, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3623, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36371 p hg
    simpa only [d8095, d3623, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36373 (p : Pattern) (guard : d8089 p = 1) : d3625 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36056 p hg
    simpa only [d8089, d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36067 p hg
    simpa only [d8089, d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36374 (p : Pattern) (guard : d5854 p = 1) : d3624 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36067 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29330 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36375 (p : Pattern) (guard : d8094 p = 1) : d3626 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36373 p hg
    simpa only [d8094, d3626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36374 p hg
    simpa only [d8094, d3626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36376 (p : Pattern) (guard : d8100 p = 1) : d3627 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36375 p hg
    simpa only [d8100, d3627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36377 (p : Pattern) (guard : d8101 p = 1) : d3628 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3628, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36372 p hg
    simpa only [d8101, d3628, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3628, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36376 p hg
    simpa only [d8101, d3628, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36378 (p : Pattern) (guard : d8102 p = 1) : d3710 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3710, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36365 p hg
    simpa only [d8102, d3710, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3710, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36377 p hg
    simpa only [d8102, d3710, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36379 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare927 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36380 (p : Pattern) (guard : d8085 p = 1) : d17 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36379 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35914 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36381 (p : Pattern) (guard : d8090 p = 1) : d17 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36380 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36017 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36382 (p : Pattern) (guard : d8095 p = 1) : d3558 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3558, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36381 p hg
    simpa only [d8095, d3558, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3558, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36319 p hg
    simpa only [d8095, d3558, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36383 (p : Pattern) (guard : d8101 p = 1) : d3563 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3563, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36382 p hg
    simpa only [d8101, d3563, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3563, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36324 p hg
    simpa only [d8101, d3563, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36384 (p : Pattern) (guard : d5854 p = 1) : d3570 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36031 p hg
    simpa only [d5854, d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29260 p hg
    simpa only [d5854, d3570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36385 (p : Pattern) (guard : d8099 p = 1) : d3571 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36384 p hg
    simpa only [d8099, d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29260 p hg
    simpa only [d8099, d3571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36386 (p : Pattern) (guard : d8105 p = 1) : d3572 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36385 p hg
    simpa only [d8105, d3572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36387 (p : Pattern) (guard : d8106 p = 1) : d3573 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36139 p hg
    simpa only [d8106, d3573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36386 p hg
    simpa only [d8106, d3573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36388 (p : Pattern) (guard : d8107 p = 1) : d3630 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3630, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36383 p hg
    simpa only [d8107, d3630, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3630, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36387 p hg
    simpa only [d8107, d3630, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36389 (p : Pattern) (guard : d8108 p = 1) : d3711 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3711, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36378 p hg
    simpa only [d8108, d3711, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3711, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36388 p hg
    simpa only [d8108, d3711, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36390 (p : Pattern) (guard : d8107 p = 1) : d3637 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3637, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36325 p hg
    simpa only [d8107, d3637, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3637, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36237 p hg
    simpa only [d8107, d3637, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36391 (p : Pattern) (guard : d8113 p = 1) : d3641 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3641, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36390 p hg
    simpa only [d8113, d3641, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3641, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36241 p hg
    simpa only [d8113, d3641, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36392 (p : Pattern) (guard : d8114 p = 1) : d3712 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3712, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36389 p hg
    simpa only [d8114, d3712, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3712, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36391 p hg
    simpa only [d8114, d3712, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36393 (p : Pattern) (guard : d8085 p = 1) : d13 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35884 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35989 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36394 (p : Pattern) (guard : d8090 p = 1) : d13 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36393 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36339 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36395 (p : Pattern) (guard : d8095 p = 1) : d3582 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3582, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36394 p hg
    simpa only [d8095, d3582, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3582, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36344 p hg
    simpa only [d8095, d3582, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36396 (p : Pattern) (guard : d8101 p = 1) : d3595 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3595, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36395 p hg
    simpa only [d8101, d3595, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3595, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36205 p hg
    simpa only [d8101, d3595, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36397 (p : Pattern) (guard : d5854 p = 1) : d30 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36125 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36398 (p : Pattern) (guard : d8094 p = 1) : d30 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36126 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36397 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36399 (p : Pattern) (guard : d5854 p = 1) : d3584 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36125 p hg
    simpa only [d5854, d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29278 p hg
    simpa only [d5854, d3584, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
