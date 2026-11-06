/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons251
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare35280 (p : Pattern) (guard : d5854 p = 1) : d116 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35279 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35281 (p : Pattern) (guard : d8099 p = 1) : d116 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35280 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35282 (p : Pattern) (guard : d8105 p = 1) : d116 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35281 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35283 (p : Pattern) (guard : d8111 p = 1) : d132 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d132, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35282 p hg
    simpa only [d8111, d132, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d132, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5171 p hg
    simpa only [d8111, d132, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35284 (p : Pattern) (guard : d8112 p = 1) : d133 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d133, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35276 p hg
    simpa only [d8112, d133, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d133, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35283 p hg
    simpa only [d8112, d133, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35285 (p : Pattern) (guard : d8117 p = 1) : d134 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35256 p hg
    simpa only [d8117, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d8117, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35286 (p : Pattern) (guard : d8118 p = 1) : d135 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d135, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35284 p hg
    simpa only [d8118, d135, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d135, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35285 p hg
    simpa only [d8118, d135, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35287 (p : Pattern) (guard : d8117 p = 1) : d136 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35256 p hg
    simpa only [d8117, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3664 p hg
    simpa only [d8117, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35288 (p : Pattern) (guard : d8123 p = 1) : d137 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35287 p hg
    simpa only [d8123, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35289 (p : Pattern) (guard : d8124 p = 1) : d138 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d138, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35286 p hg
    simpa only [d8124, d138, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d138, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35288 p hg
    simpa only [d8124, d138, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35290 (p : Pattern) (guard : d8117 p = 1) : d153 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35267 p hg
    simpa only [d8117, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35291 (p : Pattern) (guard : d8123 p = 1) : d154 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35290 p hg
    simpa only [d8123, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35292 (p : Pattern) (guard : d8129 p = 1) : d155 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35291 p hg
    simpa only [d8129, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35293 (p : Pattern) (guard : d8130 p = 1) : d156 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d156, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35289 p hg
    simpa only [d8130, d156, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d156, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35292 p hg
    simpa only [d8130, d156, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35294 (p : Pattern) (guard : d8131 p = 1) : d157 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d157, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35271 p hg
    simpa only [d8131, d157, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d157, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35293 p hg
    simpa only [d8131, d157, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35295 (p : Pattern) (guard : d8132 p = 1) : d158 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d158, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35251 p hg
    simpa only [d8132, d158, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d158, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35294 p hg
    simpa only [d8132, d158, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35296 (p : Pattern) (guard : d8137 p = 1) : d442 p ≤ (0 : Int) + d442 p := by
  omega
theorem compare35297 (p : Pattern) (guard : d8138 p = 1) : d506 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d506, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35295 p hg
    simpa only [d8138, d506, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d506, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35296 p hg
    simpa only [d8138, d506, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35298 (p : Pattern) (guard : d8084 p = 1) : d103 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d103, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35160 p hg
    simpa only [d8084, d103, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d103, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d8084, d103, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35299 (p : Pattern) (guard : d8089 p = 1) : d103 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35298 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35099 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35300 (p : Pattern) (guard : d8094 p = 1) : d103 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35299 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35114 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35301 (p : Pattern) (guard : d8100 p = 1) : d103 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35300 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35178 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35302 (p : Pattern) (guard : d8106 p = 1) : d105 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d105, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35301 p hg
    simpa only [d8106, d105, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d105, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35252 p hg
    simpa only [d8106, d105, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35303 (p : Pattern) (guard : d8107 p = 1) : d105 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35119 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35302 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35304 (p : Pattern) (guard : d5843 p = 1) : d5 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1265 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20164 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35305 (p : Pattern) (guard : d5847 p = 1) : d107 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d107, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35304 p hg
    simpa only [d5847, d107, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d107, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d107, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35306 (p : Pattern) (guard : d5854 p = 1) : d107 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35305 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35307 (p : Pattern) (guard : d8099 p = 1) : d107 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35306 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35308 (p : Pattern) (guard : d8105 p = 1) : d107 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35307 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35309 (p : Pattern) (guard : d8111 p = 1) : d109 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d109, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35308 p hg
    simpa only [d8111, d109, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d109, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5164 p hg
    simpa only [d8111, d109, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35310 (p : Pattern) (guard : d8112 p = 1) : d110 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d110, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35276 p hg
    simpa only [d8112, d110, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d110, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35309 p hg
    simpa only [d8112, d110, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35311 (p : Pattern) (guard : d8113 p = 1) : d111 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d111, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35303 p hg
    simpa only [d8113, d111, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d111, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35310 p hg
    simpa only [d8113, d111, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35312 (p : Pattern) (guard : d8112 p = 1) : d110 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d110, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35253 p hg
    simpa only [d8112, d110, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d110, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35256 p hg
    simpa only [d8112, d110, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35313 (p : Pattern) (guard : d8118 p = 1) : d113 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d113, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35312 p hg
    simpa only [d8118, d113, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d113, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35261 p hg
    simpa only [d8118, d113, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35314 (p : Pattern) (guard : d8119 p = 1) : d114 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d114, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35311 p hg
    simpa only [d8119, d114, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d114, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35313 p hg
    simpa only [d8119, d114, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35315 (p : Pattern) (guard : d8106 p = 1) : d118 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d118, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35179 p hg
    simpa only [d8106, d118, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d118, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35214 p hg
    simpa only [d8106, d118, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35316 (p : Pattern) (guard : d8105 p = 1) : d103 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35178 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35317 (p : Pattern) (guard : d8111 p = 1) : d122 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35316 p hg
    simpa only [d8111, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5173 p hg
    simpa only [d8111, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35318 (p : Pattern) (guard : d8112 p = 1) : d123 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d123, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35315 p hg
    simpa only [d8112, d123, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d123, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35317 p hg
    simpa only [d8112, d123, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35319 (p : Pattern) (guard : d8111 p = 1) : d124 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35316 p hg
    simpa only [d8111, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35320 (p : Pattern) (guard : d8117 p = 1) : d126 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35319 p hg
    simpa only [d8117, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3761 p hg
    simpa only [d8117, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35321 (p : Pattern) (guard : d8118 p = 1) : d127 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d127, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35318 p hg
    simpa only [d8118, d127, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d127, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35320 p hg
    simpa only [d8118, d127, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35322 (p : Pattern) (guard : d8123 p = 1) : d129 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35320 p hg
    simpa only [d8123, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4322 p hg
    simpa only [d8123, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35323 (p : Pattern) (guard : d8124 p = 1) : d130 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d130, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35321 p hg
    simpa only [d8124, d130, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d130, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35322 p hg
    simpa only [d8124, d130, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35324 (p : Pattern) (guard : d8125 p = 1) : d131 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d131, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35314 p hg
    simpa only [d8125, d131, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d131, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35323 p hg
    simpa only [d8125, d131, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35325 (p : Pattern) (guard : d8084 p = 1) : d103 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d103, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35144 p hg
    simpa only [d8084, d103, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d103, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d8084, d103, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35326 (p : Pattern) (guard : d8089 p = 1) : d103 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35325 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35099 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35327 (p : Pattern) (guard : d8094 p = 1) : d103 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35326 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35114 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35328 (p : Pattern) (guard : d8100 p = 1) : d103 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35327 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35178 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35329 (p : Pattern) (guard : d8106 p = 1) : d105 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d105, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35328 p hg
    simpa only [d8106, d105, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d105, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35252 p hg
    simpa only [d8106, d105, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35330 (p : Pattern) (guard : d5843 p = 1) : d3 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4566 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20196 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35331 (p : Pattern) (guard : d5847 p = 1) : d116 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d116, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35330 p hg
    simpa only [d5847, d116, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d116, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5847, d116, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35332 (p : Pattern) (guard : d5854 p = 1) : d116 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35331 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35333 (p : Pattern) (guard : d8099 p = 1) : d116 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35332 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35334 (p : Pattern) (guard : d8105 p = 1) : d116 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35333 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35335 (p : Pattern) (guard : d8111 p = 1) : d132 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d132, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35334 p hg
    simpa only [d8111, d132, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d132, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5171 p hg
    simpa only [d8111, d132, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35336 (p : Pattern) (guard : d8112 p = 1) : d133 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d133, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35329 p hg
    simpa only [d8112, d133, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d133, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35335 p hg
    simpa only [d8112, d133, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35337 (p : Pattern) (guard : d5843 p = 1) : d5 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1258 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20164 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35338 (p : Pattern) (guard : d5847 p = 1) : d107 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d107, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35337 p hg
    simpa only [d5847, d107, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d107, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d107, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35339 (p : Pattern) (guard : d5854 p = 1) : d107 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35338 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35340 (p : Pattern) (guard : d8099 p = 1) : d107 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35339 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35341 (p : Pattern) (guard : d8105 p = 1) : d107 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35340 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35342 (p : Pattern) (guard : d8111 p = 1) : d109 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d109, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35341 p hg
    simpa only [d8111, d109, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d109, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5164 p hg
    simpa only [d8111, d109, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35343 (p : Pattern) (guard : d8117 p = 1) : d134 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d134, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35342 p hg
    simpa only [d8117, d134, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d134, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d8117, d134, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35344 (p : Pattern) (guard : d8118 p = 1) : d135 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d135, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35336 p hg
    simpa only [d8118, d135, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d135, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35343 p hg
    simpa only [d8118, d135, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35345 (p : Pattern) (guard : d8117 p = 1) : d136 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d136, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35309 p hg
    simpa only [d8117, d136, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d136, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3664 p hg
    simpa only [d8117, d136, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35346 (p : Pattern) (guard : d8123 p = 1) : d137 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d137, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35345 p hg
    simpa only [d8123, d137, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d137, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d137, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35347 (p : Pattern) (guard : d8124 p = 1) : d138 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d138, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35344 p hg
    simpa only [d8124, d138, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d138, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35346 p hg
    simpa only [d8124, d138, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35348 (p : Pattern) (guard : d8117 p = 1) : d140 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35317 p hg
    simpa only [d8117, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10971 p hg
    simpa only [d8117, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35349 (p : Pattern) (guard : d0 p = 1) : d141 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35350 (p : Pattern) (guard : d8123 p = 1) : d142 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35348 p hg
    simpa only [d8123, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35349 p hg
    simpa only [d8123, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35351 (p : Pattern) (guard : d8129 p = 1) : d145 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35350 p hg
    simpa only [d8129, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13566 p hg
    simpa only [d8129, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35352 (p : Pattern) (guard : d8130 p = 1) : d146 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d146, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35347 p hg
    simpa only [d8130, d146, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d146, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35351 p hg
    simpa only [d8130, d146, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35353 (p : Pattern) (guard : d8131 p = 1) : d147 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d147, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35324 p hg
    simpa only [d8131, d147, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d147, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35352 p hg
    simpa only [d8131, d147, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35354 (p : Pattern) (guard : d8111 p = 1) : d105 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35316 p hg
    simpa only [d8111, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5162 p hg
    simpa only [d8111, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35355 (p : Pattern) (guard : d8112 p = 1) : d105 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35253 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35354 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35356 (p : Pattern) (guard : d8117 p = 1) : d110 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35354 p hg
    simpa only [d8117, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3772 p hg
    simpa only [d8117, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35357 (p : Pattern) (guard : d8118 p = 1) : d111 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d111, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35355 p hg
    simpa only [d8118, d111, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d111, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35356 p hg
    simpa only [d8118, d111, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35358 (p : Pattern) (guard : d8123 p = 1) : d113 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35356 p hg
    simpa only [d8123, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4330 p hg
    simpa only [d8123, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35359 (p : Pattern) (guard : d8124 p = 1) : d114 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d114, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35357 p hg
    simpa only [d8124, d114, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d114, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35358 p hg
    simpa only [d8124, d114, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35360 (p : Pattern) (guard : d8111 p = 1) : d132 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35241 p hg
    simpa only [d8111, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5171 p hg
    simpa only [d8111, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35361 (p : Pattern) (guard : d8117 p = 1) : d149 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35360 p hg
    simpa only [d8117, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3777 p hg
    simpa only [d8117, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35362 (p : Pattern) (guard : d8123 p = 1) : d150 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35361 p hg
    simpa only [d8123, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35363 (p : Pattern) (guard : d8129 p = 1) : d151 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35362 p hg
    simpa only [d8129, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35364 (p : Pattern) (guard : d8130 p = 1) : d152 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d152, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35359 p hg
    simpa only [d8130, d152, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d152, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35363 p hg
    simpa only [d8130, d152, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35365 (p : Pattern) (guard : d5843 p = 1) : d1 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4578 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20134 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35366 (p : Pattern) (guard : d5847 p = 1) : d103 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d103, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35365 p hg
    simpa only [d5847, d103, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d103, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5847, d103, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35367 (p : Pattern) (guard : d5854 p = 1) : d103 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35366 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35368 (p : Pattern) (guard : d8099 p = 1) : d103 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35367 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35369 (p : Pattern) (guard : d8105 p = 1) : d103 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35368 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35370 (p : Pattern) (guard : d8111 p = 1) : d105 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d105, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35369 p hg
    simpa only [d8111, d105, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d105, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5162 p hg
    simpa only [d8111, d105, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35371 (p : Pattern) (guard : d8117 p = 1) : d133 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d133, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35370 p hg
    simpa only [d8117, d133, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d133, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8230 p hg
    simpa only [d8117, d133, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35372 (p : Pattern) (guard : d8123 p = 1) : d135 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d135, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35371 p hg
    simpa only [d8123, d135, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d135, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6548 p hg
    simpa only [d8123, d135, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35373 (p : Pattern) (guard : d8129 p = 1) : d138 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d138, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35372 p hg
    simpa only [d8129, d138, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d138, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3285 p hg
    simpa only [d8129, d138, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35374 (p : Pattern) (guard : d8135 p = 1) : d156 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d156, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35373 p hg
    simpa only [d8135, d156, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d156, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4630 p hg
    simpa only [d8135, d156, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35375 (p : Pattern) (guard : d8136 p = 1) : d157 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d157, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35364 p hg
    simpa only [d8136, d157, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d157, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35374 p hg
    simpa only [d8136, d157, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35376 (p : Pattern) (guard : d8137 p = 1) : d158 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d158, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35353 p hg
    simpa only [d8137, d158, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d158, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35375 p hg
    simpa only [d8137, d158, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35377 (p : Pattern) (guard : d8142 p = 1) : d444 p ≤ (0 : Int) + d444 p := by
  omega
theorem compare35378 (p : Pattern) (guard : d8143 p = 1) : d507 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d507, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35376 p hg
    simpa only [d8143, d507, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d507, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35377 p hg
    simpa only [d8143, d507, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35379 (p : Pattern) (guard : d8144 p = 1) : d508 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d508, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35297 p hg
    simpa only [d8144, d508, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d508, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35378 p hg
    simpa only [d8144, d508, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35380 (p : Pattern) (guard : d8145 p = 1) : d509 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d509, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35082 p hg
    simpa only [d8145, d509, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d509, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35379 p hg
    simpa only [d8145, d509, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35381 (p : Pattern) (guard : d8146 p = 1) : d510 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34945 p hg
    simpa only [d8146, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35380 p hg
    simpa only [d8146, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35382 (p : Pattern) (guard : d8086 p = 1) : d14 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34745 p hg
    simpa only [d8086, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34827 p hg
    simpa only [d8086, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35383 (p : Pattern) (guard : d8091 p = 1) : d14 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35382 p hg
    simpa only [d8091, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34811 p hg
    simpa only [d8091, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35384 (p : Pattern) (guard : d8095 p = 1) : d15 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d15, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34828 p hg
    simpa only [d8095, d15, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d15, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d15, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35385 (p : Pattern) (guard : d8096 p = 1) : d16 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d16, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35383 p hg
    simpa only [d8096, d16, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d16, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35384 p hg
    simpa only [d8096, d16, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35386 (p : Pattern) (guard : d8085 p = 1) : d14 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34348 p hg
    simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34339 p hg
    simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35387 (p : Pattern) (guard : d8090 p = 1) : d14 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35386 p hg
    simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34924 p hg
    simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35388 (p : Pattern) (guard : d8095 p = 1) : d14 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35387 p hg
    simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34637 p hg
    simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35389 (p : Pattern) (guard : d8100 p = 1) : d15 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d15, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34925 p hg
    simpa only [d8100, d15, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d15, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d15, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35390 (p : Pattern) (guard : d8101 p = 1) : d16 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d16, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35388 p hg
    simpa only [d8101, d16, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d16, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35389 p hg
    simpa only [d8101, d16, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35391 (p : Pattern) (guard : d8102 p = 1) : d16 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35385 p hg
    simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35390 p hg
    simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35392 (p : Pattern) (guard : d8084 p = 1) : d18 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d18, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34379 p hg
    simpa only [d8084, d18, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d18, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d8084, d18, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35393 (p : Pattern) (guard : d8089 p = 1) : d18 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35392 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34363 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35394 (p : Pattern) (guard : d8094 p = 1) : d18 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35393 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34440 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35395 (p : Pattern) (guard : d8100 p = 1) : d18 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35394 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34642 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35396 (p : Pattern) (guard : d8106 p = 1) : d20 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d20, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35395 p hg
    simpa only [d8106, d20, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d20, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34700 p hg
    simpa only [d8106, d20, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35397 (p : Pattern) (guard : d8107 p = 1) : d21 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d21, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35042 p hg
    simpa only [d8107, d21, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d21, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35396 p hg
    simpa only [d8107, d21, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35398 (p : Pattern) (guard : d8108 p = 1) : d22 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d22, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35391 p hg
    simpa only [d8108, d22, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d22, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35397 p hg
    simpa only [d8108, d22, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35399 (p : Pattern) (guard : d8107 p = 1) : d21 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d21, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34878 p hg
    simpa only [d8107, d21, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d21, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35053 p hg
    simpa only [d8107, d21, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35400 (p : Pattern) (guard : d8112 p = 1) : d27 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d27, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34798 p hg
    simpa only [d8112, d27, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d27, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d27, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35401 (p : Pattern) (guard : d8113 p = 1) : d28 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d28, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35399 p hg
    simpa only [d8113, d28, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d28, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35400 p hg
    simpa only [d8113, d28, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35402 (p : Pattern) (guard : d8114 p = 1) : d29 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d29, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35398 p hg
    simpa only [d8114, d29, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d29, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35401 p hg
    simpa only [d8114, d29, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35403 (p : Pattern) (guard : d8101 p = 1) : d33 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d33, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34846 p hg
    simpa only [d8101, d33, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d33, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34589 p hg
    simpa only [d8101, d33, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35404 (p : Pattern) (guard : d8106 p = 1) : d37 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d37, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35072 p hg
    simpa only [d8106, d37, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d37, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34711 p hg
    simpa only [d8106, d37, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35405 (p : Pattern) (guard : d8107 p = 1) : d38 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d38, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35403 p hg
    simpa only [d8107, d38, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d38, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35404 p hg
    simpa only [d8107, d38, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35406 (p : Pattern) (guard : d8106 p = 1) : d42 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d42, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34926 p hg
    simpa only [d8106, d42, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d42, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34605 p hg
    simpa only [d8106, d42, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35407 (p : Pattern) (guard : d8112 p = 1) : d44 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d44, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35406 p hg
    simpa only [d8112, d44, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d44, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d8112, d44, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35408 (p : Pattern) (guard : d8113 p = 1) : d45 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d45, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35405 p hg
    simpa only [d8113, d45, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d45, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35407 p hg
    simpa only [d8113, d45, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35409 (p : Pattern) (guard : d8119 p = 1) : d51 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d51, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35408 p hg
    simpa only [d8119, d51, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d51, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34872 p hg
    simpa only [d8119, d51, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35410 (p : Pattern) (guard : d8120 p = 1) : d52 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d52, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35402 p hg
    simpa only [d8120, d52, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d52, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35409 p hg
    simpa only [d8120, d52, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35411 (p : Pattern) (guard : d8085 p = 1) : d14 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34331 p hg
    simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34923 p hg
    simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35412 (p : Pattern) (guard : d8090 p = 1) : d14 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35411 p hg
    simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35070 p hg
    simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35413 (p : Pattern) (guard : d8095 p = 1) : d14 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35412 p hg
    simpa only [d8095, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34925 p hg
    simpa only [d8095, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35414 (p : Pattern) (guard : d8100 p = 1) : d15 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d15, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35071 p hg
    simpa only [d8100, d15, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d15, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d15, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35415 (p : Pattern) (guard : d8101 p = 1) : d16 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d16, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35413 p hg
    simpa only [d8101, d16, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d16, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35414 p hg
    simpa only [d8101, d16, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35416 (p : Pattern) (guard : d8084 p = 1) : d31 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d31, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34783 p hg
    simpa only [d8084, d31, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d31, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d8084, d31, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35417 (p : Pattern) (guard : d8089 p = 1) : d31 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35416 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34472 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35418 (p : Pattern) (guard : d8094 p = 1) : d31 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35417 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34525 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35419 (p : Pattern) (guard : d8100 p = 1) : d31 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35418 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34678 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
