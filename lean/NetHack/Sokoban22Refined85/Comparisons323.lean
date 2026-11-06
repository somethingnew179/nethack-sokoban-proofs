/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons322
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare45220 (p : Pattern) (guard : d8089 p = 1) : d3374 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45218 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45219 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45221 (p : Pattern) (guard : d5854 p = 1) : d3374 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45219 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45222 (p : Pattern) (guard : d8094 p = 1) : d3374 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45220 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45221 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45223 (p : Pattern) (guard : d8100 p = 1) : d3375 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45222 p hg
    simpa only [d8100, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45224 (p : Pattern) (guard : d8101 p = 1) : d3376 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3376, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45217 p hg
    simpa only [d8101, d3376, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3376, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45223 p hg
    simpa only [d8101, d3376, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45225 (p : Pattern) (guard : d8084 p = 1) : d3358 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3358, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35174 p hg
    simpa only [d8084, d3358, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3358, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3358, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45226 (p : Pattern) (guard : d8089 p = 1) : d3358 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45225 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45164 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45227 (p : Pattern) (guard : d8094 p = 1) : d3358 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45226 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45176 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45228 (p : Pattern) (guard : d8099 p = 1) : d3358 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45176 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45229 (p : Pattern) (guard : d8100 p = 1) : d3358 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45227 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45228 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45230 (p : Pattern) (guard : d5847 p = 1) : d3377 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35180 p hg
    simpa only [d5847, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45231 (p : Pattern) (guard : d5854 p = 1) : d3377 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45230 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26801 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45232 (p : Pattern) (guard : d8099 p = 1) : d3377 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45231 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26801 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45233 (p : Pattern) (guard : d8105 p = 1) : d3378 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45232 p hg
    simpa only [d8105, d3378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45234 (p : Pattern) (guard : d8106 p = 1) : d3379 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3379, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45229 p hg
    simpa only [d8106, d3379, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3379, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45233 p hg
    simpa only [d8106, d3379, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45235 (p : Pattern) (guard : d8107 p = 1) : d3380 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3380, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45224 p hg
    simpa only [d8107, d3380, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3380, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45234 p hg
    simpa only [d8107, d3380, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45236 (p : Pattern) (guard : d8100 p = 1) : d3358 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45179 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45228 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45237 (p : Pattern) (guard : d8106 p = 1) : d3381 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3381, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45236 p hg
    simpa only [d8106, d3381, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3381, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3381, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45238 (p : Pattern) (guard : d8105 p = 1) : d3366 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45194 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45239 (p : Pattern) (guard : d8111 p = 1) : d3382 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45238 p hg
    simpa only [d8111, d3382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45240 (p : Pattern) (guard : d8112 p = 1) : d3383 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3383, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45237 p hg
    simpa only [d8112, d3383, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3383, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45239 p hg
    simpa only [d8112, d3383, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45241 (p : Pattern) (guard : d8113 p = 1) : d3384 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3384, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45235 p hg
    simpa only [d8113, d3384, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3384, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45240 p hg
    simpa only [d8113, d3384, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45242 (p : Pattern) (guard : d8100 p = 1) : d3358 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45177 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45228 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45243 (p : Pattern) (guard : d8106 p = 1) : d3381 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45242 p hg
    simpa only [d8106, d3381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45244 (p : Pattern) (guard : d8112 p = 1) : d3383 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45243 p hg
    simpa only [d8112, d3383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45239 p hg
    simpa only [d8112, d3383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45245 (p : Pattern) (guard : d8117 p = 1) : d3385 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44711 p hg
    simpa only [d8117, d3385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45246 (p : Pattern) (guard : d8118 p = 1) : d3386 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45244 p hg
    simpa only [d8118, d3386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45245 p hg
    simpa only [d8118, d3386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45247 (p : Pattern) (guard : d8119 p = 1) : d3387 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3387, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45241 p hg
    simpa only [d8119, d3387, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3387, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45246 p hg
    simpa only [d8119, d3387, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45248 (p : Pattern) (guard : d8120 p = 1) : d3388 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3388, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45213 p hg
    simpa only [d8120, d3388, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3388, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45247 p hg
    simpa only [d8120, d3388, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45249 (p : Pattern) (guard : d1 p = 1) : d3389 p ≤ (0 : Int) + d326 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3389, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35200 p hg
    simpa only [d3389, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3389, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36103 p hg
    simpa only [d3389, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45250 (p : Pattern) (guard : d8085 p = 1) : d3390 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3390, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45249 p hg
    simpa only [d8085, d3390, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3390, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45173 p hg
    simpa only [d8085, d3390, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45251 (p : Pattern) (guard : d8090 p = 1) : d3391 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3391, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45250 p hg
    simpa only [d8090, d3391, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3391, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45226 p hg
    simpa only [d8090, d3391, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45252 (p : Pattern) (guard : d8095 p = 1) : d3392 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3392, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45251 p hg
    simpa only [d8095, d3392, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3392, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45179 p hg
    simpa only [d8095, d3392, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45253 (p : Pattern) (guard : d8100 p = 1) : d3362 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3362, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45227 p hg
    simpa only [d8100, d3362, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3362, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3362, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45254 (p : Pattern) (guard : d8101 p = 1) : d3393 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3393, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45252 p hg
    simpa only [d8101, d3393, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3393, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45253 p hg
    simpa only [d8101, d3393, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45255 (p : Pattern) (guard : d8084 p = 1) : d3374 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3374, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35208 p hg
    simpa only [d8084, d3374, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3374, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3374, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45256 (p : Pattern) (guard : d8089 p = 1) : d3374 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45255 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45219 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45257 (p : Pattern) (guard : d8094 p = 1) : d3374 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45256 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45221 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45258 (p : Pattern) (guard : d8099 p = 1) : d3374 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45221 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45259 (p : Pattern) (guard : d8100 p = 1) : d3374 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45257 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45258 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45260 (p : Pattern) (guard : d8105 p = 1) : d3375 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45258 p hg
    simpa only [d8105, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45261 (p : Pattern) (guard : d8106 p = 1) : d3394 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3394, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45259 p hg
    simpa only [d8106, d3394, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3394, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d8106, d3394, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45262 (p : Pattern) (guard : d8107 p = 1) : d3395 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3395, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45254 p hg
    simpa only [d8107, d3395, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3395, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d8107, d3395, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45263 (p : Pattern) (guard : d8084 p = 1) : d3366 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3366, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35217 p hg
    simpa only [d8084, d3366, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3366, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3366, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45264 (p : Pattern) (guard : d8089 p = 1) : d3366 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45190 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45265 (p : Pattern) (guard : d8094 p = 1) : d3366 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45192 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45266 (p : Pattern) (guard : d8100 p = 1) : d3366 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45265 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45194 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45267 (p : Pattern) (guard : d8106 p = 1) : d3368 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3368, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45266 p hg
    simpa only [d8106, d3368, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3368, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45196 p hg
    simpa only [d8106, d3368, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45268 (p : Pattern) (guard : d8099 p = 1) : d3279 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28840 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26681 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45269 (p : Pattern) (guard : d8105 p = 1) : d3279 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26681 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45270 (p : Pattern) (guard : d8111 p = 1) : d3281 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3281, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45269 p hg
    simpa only [d8111, d3281, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3281, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44752 p hg
    simpa only [d8111, d3281, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45271 (p : Pattern) (guard : d8112 p = 1) : d3396 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3396, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45267 p hg
    simpa only [d8112, d3396, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3396, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45270 p hg
    simpa only [d8112, d3396, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45272 (p : Pattern) (guard : d8113 p = 1) : d3397 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3397, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d8113, d3397, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3397, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45271 p hg
    simpa only [d8113, d3397, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45273 (p : Pattern) (guard : d8099 p = 1) : d3257 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28803 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26655 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45274 (p : Pattern) (guard : d8105 p = 1) : d3257 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45273 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26655 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45275 (p : Pattern) (guard : d8111 p = 1) : d3283 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3283, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45274 p hg
    simpa only [d8111, d3283, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3283, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44755 p hg
    simpa only [d8111, d3283, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45276 (p : Pattern) (guard : d8112 p = 1) : d3398 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3398, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45197 p hg
    simpa only [d8112, d3398, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3398, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45275 p hg
    simpa only [d8112, d3398, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45277 (p : Pattern) (guard : d8118 p = 1) : d3399 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3399, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45276 p hg
    simpa only [d8118, d3399, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3399, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d3399, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45278 (p : Pattern) (guard : d8119 p = 1) : d3400 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3400, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45272 p hg
    simpa only [d8119, d3400, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3400, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45277 p hg
    simpa only [d8119, d3400, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45279 (p : Pattern) (guard : d8084 p = 1) : d3358 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3358, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35087 p hg
    simpa only [d8084, d3358, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3358, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3358, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45280 (p : Pattern) (guard : d8089 p = 1) : d3358 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45279 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45164 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45281 (p : Pattern) (guard : d8094 p = 1) : d3358 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45280 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45176 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45282 (p : Pattern) (guard : d8100 p = 1) : d3358 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45281 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45228 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45283 (p : Pattern) (guard : d8106 p = 1) : d3379 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3379, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d8106, d3379, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3379, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45233 p hg
    simpa only [d8106, d3379, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45284 (p : Pattern) (guard : d8105 p = 1) : d3374 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45258 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45285 (p : Pattern) (guard : d8111 p = 1) : d3401 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45284 p hg
    simpa only [d8111, d3401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45286 (p : Pattern) (guard : d8112 p = 1) : d3402 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3402, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45283 p hg
    simpa only [d8112, d3402, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3402, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45285 p hg
    simpa only [d8112, d3402, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45287 (p : Pattern) (guard : d8117 p = 1) : d3403 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45239 p hg
    simpa only [d8117, d3403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44960 p hg
    simpa only [d8117, d3403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45288 (p : Pattern) (guard : d8118 p = 1) : d3404 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3404, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45286 p hg
    simpa only [d8118, d3404, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3404, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45287 p hg
    simpa only [d8118, d3404, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45289 (p : Pattern) (guard : d0 p = 1) : d3293 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45290 (p : Pattern) (guard : d8117 p = 1) : d3405 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45239 p hg
    simpa only [d8117, d3405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45289 p hg
    simpa only [d8117, d3405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45291 (p : Pattern) (guard : d8123 p = 1) : d3406 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45290 p hg
    simpa only [d8123, d3406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45292 (p : Pattern) (guard : d8124 p = 1) : d3407 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3407, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45288 p hg
    simpa only [d8124, d3407, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3407, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45291 p hg
    simpa only [d8124, d3407, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45293 (p : Pattern) (guard : d8125 p = 1) : d3408 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3408, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45278 p hg
    simpa only [d8125, d3408, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3408, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45292 p hg
    simpa only [d8125, d3408, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45294 (p : Pattern) (guard : d8126 p = 1) : d3409 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3409, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45248 p hg
    simpa only [d8126, d3409, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3409, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45293 p hg
    simpa only [d8126, d3409, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45295 (p : Pattern) (guard : d8105 p = 1) : d3362 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45228 p hg
    simpa only [d8105, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45296 (p : Pattern) (guard : d8106 p = 1) : d3364 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3364, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d8106, d3364, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3364, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45295 p hg
    simpa only [d8106, d3364, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45297 (p : Pattern) (guard : d8107 p = 1) : d3364 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45204 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45296 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45298 (p : Pattern) (guard : d8106 p = 1) : d3364 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3364, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45229 p hg
    simpa only [d8106, d3364, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3364, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45295 p hg
    simpa only [d8106, d3364, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45299 (p : Pattern) (guard : d0 p = 1) : d3367 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45300 (p : Pattern) (guard : d8111 p = 1) : d3368 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45238 p hg
    simpa only [d8111, d3368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d8111, d3368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45301 (p : Pattern) (guard : d8112 p = 1) : d3369 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3369, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45298 p hg
    simpa only [d8112, d3369, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3369, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45300 p hg
    simpa only [d8112, d3369, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45302 (p : Pattern) (guard : d8113 p = 1) : d3410 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3410, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45297 p hg
    simpa only [d8113, d3410, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3410, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45301 p hg
    simpa only [d8113, d3410, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45303 (p : Pattern) (guard : d8106 p = 1) : d3364 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3364, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45236 p hg
    simpa only [d8106, d3364, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3364, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45295 p hg
    simpa only [d8106, d3364, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45304 (p : Pattern) (guard : d8112 p = 1) : d3369 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3369, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45303 p hg
    simpa only [d8112, d3369, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3369, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45300 p hg
    simpa only [d8112, d3369, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45305 (p : Pattern) (guard : d8117 p = 1) : d3371 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44753 p hg
    simpa only [d8117, d3371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45306 (p : Pattern) (guard : d8118 p = 1) : d3372 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3372, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45304 p hg
    simpa only [d8118, d3372, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3372, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45305 p hg
    simpa only [d8118, d3372, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45307 (p : Pattern) (guard : d8119 p = 1) : d3411 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3411, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45302 p hg
    simpa only [d8119, d3411, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3411, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45306 p hg
    simpa only [d8119, d3411, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45308 (p : Pattern) (guard : d8100 p = 1) : d3374 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45222 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45258 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45309 (p : Pattern) (guard : d8106 p = 1) : d3394 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45308 p hg
    simpa only [d8106, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d8106, d3394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45310 (p : Pattern) (guard : d8105 p = 1) : d3377 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45232 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26801 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45311 (p : Pattern) (guard : d0 p = 1) : d3378 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45312 (p : Pattern) (guard : d8111 p = 1) : d3412 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45310 p hg
    simpa only [d8111, d3412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45311 p hg
    simpa only [d8111, d3412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45313 (p : Pattern) (guard : d8112 p = 1) : d3413 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45309 p hg
    simpa only [d8112, d3413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45312 p hg
    simpa only [d8112, d3413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45314 (p : Pattern) (guard : d8118 p = 1) : d3414 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45313 p hg
    simpa only [d8118, d3414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d3414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45315 (p : Pattern) (guard : d8124 p = 1) : d3415 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45314 p hg
    simpa only [d8124, d3415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45316 (p : Pattern) (guard : d8125 p = 1) : d3416 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3416, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45307 p hg
    simpa only [d8125, d3416, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3416, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45315 p hg
    simpa only [d8125, d3416, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45317 (p : Pattern) (guard : d8084 p = 1) : d3358 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3358, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35091 p hg
    simpa only [d8084, d3358, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3358, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3358, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45318 (p : Pattern) (guard : d8089 p = 1) : d3358 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45317 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45164 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45319 (p : Pattern) (guard : d8094 p = 1) : d3358 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45318 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45176 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45320 (p : Pattern) (guard : d8100 p = 1) : d3358 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45319 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45228 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45321 (p : Pattern) (guard : d8106 p = 1) : d3364 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3364, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45320 p hg
    simpa only [d8106, d3364, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3364, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45295 p hg
    simpa only [d8106, d3364, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45322 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3374, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35278 p hg
    simpa only [d5847, d3374, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3374, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3374, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45323 (p : Pattern) (guard : d5854 p = 1) : d3374 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45322 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45324 (p : Pattern) (guard : d8099 p = 1) : d3374 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45323 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45325 (p : Pattern) (guard : d8105 p = 1) : d3374 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45324 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26796 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45326 (p : Pattern) (guard : d0 p = 1) : d3375 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45327 (p : Pattern) (guard : d8111 p = 1) : d3394 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3394, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45325 p hg
    simpa only [d8111, d3394, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3394, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45326 p hg
    simpa only [d8111, d3394, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45328 (p : Pattern) (guard : d8112 p = 1) : d3417 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3417, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45321 p hg
    simpa only [d8112, d3417, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3417, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45327 p hg
    simpa only [d8112, d3417, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45329 (p : Pattern) (guard : d8117 p = 1) : d3396 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45300 p hg
    simpa only [d8117, d3396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44995 p hg
    simpa only [d8117, d3396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45330 (p : Pattern) (guard : d8118 p = 1) : d3418 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3418, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45328 p hg
    simpa only [d8118, d3418, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3418, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45329 p hg
    simpa only [d8118, d3418, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45331 (p : Pattern) (guard : d0 p = 1) : d3283 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45332 (p : Pattern) (guard : d8117 p = 1) : d3398 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45300 p hg
    simpa only [d8117, d3398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45331 p hg
    simpa only [d8117, d3398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45333 (p : Pattern) (guard : d8123 p = 1) : d3399 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45332 p hg
    simpa only [d8123, d3399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45334 (p : Pattern) (guard : d8124 p = 1) : d3419 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3419, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45330 p hg
    simpa only [d8124, d3419, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3419, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45333 p hg
    simpa only [d8124, d3419, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45335 (p : Pattern) (guard : d8117 p = 1) : d3420 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45312 p hg
    simpa only [d8117, d3420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45336 (p : Pattern) (guard : d8123 p = 1) : d3421 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45335 p hg
    simpa only [d8123, d3421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45337 (p : Pattern) (guard : d8129 p = 1) : d3422 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45336 p hg
    simpa only [d8129, d3422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45338 (p : Pattern) (guard : d8130 p = 1) : d3423 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3423, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45334 p hg
    simpa only [d8130, d3423, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3423, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45337 p hg
    simpa only [d8130, d3423, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45339 (p : Pattern) (guard : d8131 p = 1) : d3424 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3424, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45316 p hg
    simpa only [d8131, d3424, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3424, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d8131, d3424, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45340 (p : Pattern) (guard : d8132 p = 1) : d3425 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d3425, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45294 p hg
    simpa only [d8132, d3425, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d3425, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d8132, d3425, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45341 (p : Pattern) (guard : d8107 p = 1) : d3364 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45188 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45321 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45342 (p : Pattern) (guard : d8112 p = 1) : d3369 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3369, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45296 p hg
    simpa only [d8112, d3369, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3369, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45300 p hg
    simpa only [d8112, d3369, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45343 (p : Pattern) (guard : d8113 p = 1) : d3410 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3410, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45341 p hg
    simpa only [d8113, d3410, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3410, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45342 p hg
    simpa only [d8113, d3410, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45344 (p : Pattern) (guard : d8118 p = 1) : d3372 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3372, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45301 p hg
    simpa only [d8118, d3372, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3372, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45305 p hg
    simpa only [d8118, d3372, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45345 (p : Pattern) (guard : d8119 p = 1) : d3411 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3411, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45343 p hg
    simpa only [d8119, d3411, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3411, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45344 p hg
    simpa only [d8119, d3411, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45346 (p : Pattern) (guard : d8084 p = 1) : d3374 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3374, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38205 p hg
    simpa only [d8084, d3374, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3374, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3374, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45347 (p : Pattern) (guard : d8089 p = 1) : d3374 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45346 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45219 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45348 (p : Pattern) (guard : d8094 p = 1) : d3374 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45347 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45221 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45349 (p : Pattern) (guard : d8100 p = 1) : d3374 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45348 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45258 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45350 (p : Pattern) (guard : d8106 p = 1) : d3394 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3394, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45349 p hg
    simpa only [d8106, d3394, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3394, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d8106, d3394, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45351 (p : Pattern) (guard : d8112 p = 1) : d3413 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3413, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45350 p hg
    simpa only [d8112, d3413, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3413, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45312 p hg
    simpa only [d8112, d3413, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45352 (p : Pattern) (guard : d8118 p = 1) : d3414 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3414, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45351 p hg
    simpa only [d8118, d3414, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3414, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d3414, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45353 (p : Pattern) (guard : d8124 p = 1) : d3415 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3415, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45352 p hg
    simpa only [d8124, d3415, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3415, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3415, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45354 (p : Pattern) (guard : d8125 p = 1) : d3416 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3416, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45345 p hg
    simpa only [d8125, d3416, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3416, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45353 p hg
    simpa only [d8125, d3416, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45355 (p : Pattern) (guard : d8084 p = 1) : d3358 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3358, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35160 p hg
    simpa only [d8084, d3358, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3358, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3358, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45356 (p : Pattern) (guard : d8089 p = 1) : d3358 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45355 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45164 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45357 (p : Pattern) (guard : d8094 p = 1) : d3358 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45356 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45176 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45358 (p : Pattern) (guard : d8100 p = 1) : d3358 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45357 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45228 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45359 (p : Pattern) (guard : d8106 p = 1) : d3364 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3364, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45358 p hg
    simpa only [d8106, d3364, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3364, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45295 p hg
    simpa only [d8106, d3364, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
