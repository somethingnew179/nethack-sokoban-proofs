/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons252
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare35420 (p : Pattern) (guard : d8106 p = 1) : d53 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d53, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35419 p hg
    simpa only [d8106, d53, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d53, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34721 p hg
    simpa only [d8106, d53, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35421 (p : Pattern) (guard : d8107 p = 1) : d54 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d54, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35415 p hg
    simpa only [d8107, d54, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d54, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35420 p hg
    simpa only [d8107, d54, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35422 (p : Pattern) (guard : d8084 p = 1) : d18 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d18, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34355 p hg
    simpa only [d8084, d18, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d18, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d8084, d18, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35423 (p : Pattern) (guard : d8089 p = 1) : d18 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35422 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34363 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35424 (p : Pattern) (guard : d8094 p = 1) : d18 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35423 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34440 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35425 (p : Pattern) (guard : d8100 p = 1) : d18 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35424 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34642 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35426 (p : Pattern) (guard : d8106 p = 1) : d20 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d20, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35425 p hg
    simpa only [d8106, d20, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d20, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34700 p hg
    simpa only [d8106, d20, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35427 (p : Pattern) (guard : d5843 p = 1) : d9 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare690 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19887 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35428 (p : Pattern) (guard : d5847 p = 1) : d24 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d24, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35427 p hg
    simpa only [d5847, d24, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d24, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5847, d24, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35429 (p : Pattern) (guard : d5854 p = 1) : d24 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35428 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11467 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35430 (p : Pattern) (guard : d8099 p = 1) : d24 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35429 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11467 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35431 (p : Pattern) (guard : d8105 p = 1) : d24 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35430 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11467 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35432 (p : Pattern) (guard : d8111 p = 1) : d26 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d26, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35431 p hg
    simpa only [d8111, d26, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d26, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5057 p hg
    simpa only [d8111, d26, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35433 (p : Pattern) (guard : d8112 p = 1) : d55 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d55, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35426 p hg
    simpa only [d8112, d55, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d55, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35432 p hg
    simpa only [d8112, d55, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35434 (p : Pattern) (guard : d8113 p = 1) : d56 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d56, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35421 p hg
    simpa only [d8113, d56, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d56, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35433 p hg
    simpa only [d8113, d56, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35435 (p : Pattern) (guard : d5843 p = 1) : d10 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19990 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35436 (p : Pattern) (guard : d5847 p = 1) : d58 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d58, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35435 p hg
    simpa only [d5847, d58, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d58, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5847, d58, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35437 (p : Pattern) (guard : d5854 p = 1) : d58 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35436 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11502 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35438 (p : Pattern) (guard : d8099 p = 1) : d58 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35437 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11502 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35439 (p : Pattern) (guard : d8105 p = 1) : d58 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35438 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11502 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35440 (p : Pattern) (guard : d8111 p = 1) : d60 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d60, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35439 p hg
    simpa only [d8111, d60, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d60, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5081 p hg
    simpa only [d8111, d60, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35441 (p : Pattern) (guard : d8112 p = 1) : d61 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d61, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35396 p hg
    simpa only [d8112, d61, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d61, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35440 p hg
    simpa only [d8112, d61, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35442 (p : Pattern) (guard : d8118 p = 1) : d64 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d64, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35441 p hg
    simpa only [d8118, d64, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d64, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d64, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35443 (p : Pattern) (guard : d8119 p = 1) : d65 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d65, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35434 p hg
    simpa only [d8119, d65, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d65, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35442 p hg
    simpa only [d8119, d65, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35444 (p : Pattern) (guard : d8084 p = 1) : d14 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d14, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33853 p hg
    simpa only [d8084, d14, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d14, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d8084, d14, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35445 (p : Pattern) (guard : d8089 p = 1) : d14 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35444 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34416 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35446 (p : Pattern) (guard : d8094 p = 1) : d14 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35445 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34636 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35447 (p : Pattern) (guard : d8100 p = 1) : d14 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35446 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35448 (p : Pattern) (guard : d8106 p = 1) : d37 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d37, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35447 p hg
    simpa only [d8106, d37, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d37, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34711 p hg
    simpa only [d8106, d37, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35449 (p : Pattern) (guard : d8112 p = 1) : d67 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d67, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35448 p hg
    simpa only [d8112, d67, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d67, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34897 p hg
    simpa only [d8112, d67, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35450 (p : Pattern) (guard : d8118 p = 1) : d69 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d69, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35449 p hg
    simpa only [d8118, d69, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d69, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d8118, d69, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35451 (p : Pattern) (guard : d8124 p = 1) : d75 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d75, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35450 p hg
    simpa only [d8124, d75, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d75, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34904 p hg
    simpa only [d8124, d75, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35452 (p : Pattern) (guard : d8125 p = 1) : d76 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d76, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35443 p hg
    simpa only [d8125, d76, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d76, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35451 p hg
    simpa only [d8125, d76, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35453 (p : Pattern) (guard : d8126 p = 1) : d77 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d77, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35410 p hg
    simpa only [d8126, d77, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d77, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35452 p hg
    simpa only [d8126, d77, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35454 (p : Pattern) (guard : d8106 p = 1) : d16 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d16, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35447 p hg
    simpa only [d8106, d16, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d16, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34908 p hg
    simpa only [d8106, d16, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35455 (p : Pattern) (guard : d8107 p = 1) : d16 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34878 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35454 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35456 (p : Pattern) (guard : d8112 p = 1) : d21 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d21, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35073 p hg
    simpa only [d8112, d21, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d21, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34911 p hg
    simpa only [d8112, d21, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35457 (p : Pattern) (guard : d8113 p = 1) : d22 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d22, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35455 p hg
    simpa only [d8113, d22, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d22, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35456 p hg
    simpa only [d8113, d22, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35458 (p : Pattern) (guard : d8112 p = 1) : d21 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d21, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34927 p hg
    simpa only [d8112, d21, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d21, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34911 p hg
    simpa only [d8112, d21, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35459 (p : Pattern) (guard : d8118 p = 1) : d28 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d28, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35458 p hg
    simpa only [d8118, d28, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d28, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d8118, d28, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35460 (p : Pattern) (guard : d8119 p = 1) : d29 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d29, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35457 p hg
    simpa only [d8119, d29, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d29, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35459 p hg
    simpa only [d8119, d29, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35461 (p : Pattern) (guard : d8125 p = 1) : d82 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d82, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35460 p hg
    simpa only [d8125, d82, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d82, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34921 p hg
    simpa only [d8125, d82, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35462 (p : Pattern) (guard : d8084 p = 1) : d14 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d14, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33795 p hg
    simpa only [d8084, d14, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d14, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d8084, d14, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35463 (p : Pattern) (guard : d8089 p = 1) : d14 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35462 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34416 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35464 (p : Pattern) (guard : d8094 p = 1) : d14 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35463 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34636 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35465 (p : Pattern) (guard : d8100 p = 1) : d14 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35464 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35466 (p : Pattern) (guard : d8106 p = 1) : d16 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d16, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35465 p hg
    simpa only [d8106, d16, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d16, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34908 p hg
    simpa only [d8106, d16, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35467 (p : Pattern) (guard : d5843 p = 1) : d2 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1532 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19915 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35468 (p : Pattern) (guard : d5847 p = 1) : d31 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d31, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35467 p hg
    simpa only [d5847, d31, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d31, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5847, d31, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35469 (p : Pattern) (guard : d5854 p = 1) : d31 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35468 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35470 (p : Pattern) (guard : d8099 p = 1) : d31 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35469 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35471 (p : Pattern) (guard : d8105 p = 1) : d31 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35470 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35472 (p : Pattern) (guard : d8111 p = 1) : d53 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d53, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35471 p hg
    simpa only [d8111, d53, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d53, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5062 p hg
    simpa only [d8111, d53, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35473 (p : Pattern) (guard : d8112 p = 1) : d54 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d54, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35466 p hg
    simpa only [d8112, d54, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d54, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35472 p hg
    simpa only [d8112, d54, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35474 (p : Pattern) (guard : d8118 p = 1) : d56 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d56, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35473 p hg
    simpa only [d8118, d56, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d56, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34931 p hg
    simpa only [d8118, d56, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35475 (p : Pattern) (guard : d8124 p = 1) : d65 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d65, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35474 p hg
    simpa only [d8124, d65, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d65, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34934 p hg
    simpa only [d8124, d65, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35476 (p : Pattern) (guard : d8130 p = 1) : d86 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d86, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35475 p hg
    simpa only [d8130, d86, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d86, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34938 p hg
    simpa only [d8130, d86, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35477 (p : Pattern) (guard : d8131 p = 1) : d87 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d87, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35461 p hg
    simpa only [d8131, d87, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d87, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35476 p hg
    simpa only [d8131, d87, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35478 (p : Pattern) (guard : d8132 p = 1) : d88 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d88, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35453 p hg
    simpa only [d8132, d88, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d88, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35477 p hg
    simpa only [d8132, d88, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35479 (p : Pattern) (guard : d8138 p = 1) : d502 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d502, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35478 p hg
    simpa only [d8138, d502, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d502, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35296 p hg
    simpa only [d8138, d502, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35480 (p : Pattern) (guard : d8084 p = 1) : d14 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d14, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33799 p hg
    simpa only [d8084, d14, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d14, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d8084, d14, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35481 (p : Pattern) (guard : d8089 p = 1) : d14 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35480 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34416 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35482 (p : Pattern) (guard : d8094 p = 1) : d14 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35481 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34636 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35483 (p : Pattern) (guard : d8100 p = 1) : d14 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35482 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35484 (p : Pattern) (guard : d8106 p = 1) : d16 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d16, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35483 p hg
    simpa only [d8106, d16, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d16, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34908 p hg
    simpa only [d8106, d16, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35485 (p : Pattern) (guard : d8107 p = 1) : d16 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35390 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35484 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35486 (p : Pattern) (guard : d5843 p = 1) : d4 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare937 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19859 p hg
    simpa only [d5843, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35487 (p : Pattern) (guard : d5847 p = 1) : d18 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d18, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35486 p hg
    simpa only [d5847, d18, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d18, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5847, d18, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35488 (p : Pattern) (guard : d5854 p = 1) : d18 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35487 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11461 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35489 (p : Pattern) (guard : d8099 p = 1) : d18 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35488 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11461 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35490 (p : Pattern) (guard : d8105 p = 1) : d18 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35489 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11461 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35491 (p : Pattern) (guard : d8111 p = 1) : d20 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d20, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35490 p hg
    simpa only [d8111, d20, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d20, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5050 p hg
    simpa only [d8111, d20, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35492 (p : Pattern) (guard : d8112 p = 1) : d21 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d21, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35466 p hg
    simpa only [d8112, d21, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d21, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35491 p hg
    simpa only [d8112, d21, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35493 (p : Pattern) (guard : d8113 p = 1) : d22 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d22, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35485 p hg
    simpa only [d8113, d22, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d22, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35492 p hg
    simpa only [d8113, d22, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35494 (p : Pattern) (guard : d8112 p = 1) : d21 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d21, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35454 p hg
    simpa only [d8112, d21, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d21, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34911 p hg
    simpa only [d8112, d21, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35495 (p : Pattern) (guard : d8118 p = 1) : d28 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d28, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35494 p hg
    simpa only [d8118, d28, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d28, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d8118, d28, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35496 (p : Pattern) (guard : d8119 p = 1) : d29 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d29, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35493 p hg
    simpa only [d8119, d29, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d29, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35495 p hg
    simpa only [d8119, d29, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35497 (p : Pattern) (guard : d8106 p = 1) : d33 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d33, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35072 p hg
    simpa only [d8106, d33, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d33, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34721 p hg
    simpa only [d8106, d33, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35498 (p : Pattern) (guard : d8105 p = 1) : d14 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11458 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35499 (p : Pattern) (guard : d8111 p = 1) : d37 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35498 p hg
    simpa only [d8111, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5064 p hg
    simpa only [d8111, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35500 (p : Pattern) (guard : d8112 p = 1) : d38 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d38, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35497 p hg
    simpa only [d8112, d38, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d38, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35499 p hg
    simpa only [d8112, d38, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35501 (p : Pattern) (guard : d8111 p = 1) : d42 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35498 p hg
    simpa only [d8111, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5067 p hg
    simpa only [d8111, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35502 (p : Pattern) (guard : d8117 p = 1) : d44 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35501 p hg
    simpa only [d8117, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3627 p hg
    simpa only [d8117, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35503 (p : Pattern) (guard : d8118 p = 1) : d45 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d45, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35500 p hg
    simpa only [d8118, d45, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d45, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35502 p hg
    simpa only [d8118, d45, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35504 (p : Pattern) (guard : d8111 p = 1) : d46 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35498 p hg
    simpa only [d8111, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35505 (p : Pattern) (guard : d8117 p = 1) : d47 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35504 p hg
    simpa only [d8117, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3627 p hg
    simpa only [d8117, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35506 (p : Pattern) (guard : d8123 p = 1) : d50 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35505 p hg
    simpa only [d8123, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4221 p hg
    simpa only [d8123, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35507 (p : Pattern) (guard : d8124 p = 1) : d51 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d51, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35503 p hg
    simpa only [d8124, d51, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d51, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35506 p hg
    simpa only [d8124, d51, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35508 (p : Pattern) (guard : d8125 p = 1) : d52 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d52, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35496 p hg
    simpa only [d8125, d52, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d52, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35507 p hg
    simpa only [d8125, d52, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35509 (p : Pattern) (guard : d8084 p = 1) : d14 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d14, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33863 p hg
    simpa only [d8084, d14, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d14, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d8084, d14, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35510 (p : Pattern) (guard : d8089 p = 1) : d14 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35509 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34416 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35511 (p : Pattern) (guard : d8094 p = 1) : d14 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35510 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34636 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35512 (p : Pattern) (guard : d8100 p = 1) : d14 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35511 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d8100, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35513 (p : Pattern) (guard : d8106 p = 1) : d16 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d16, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35512 p hg
    simpa only [d8106, d16, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d16, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34908 p hg
    simpa only [d8106, d16, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35514 (p : Pattern) (guard : d5843 p = 1) : d2 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10843 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19915 p hg
    simpa only [d5843, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35515 (p : Pattern) (guard : d5847 p = 1) : d31 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d31, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35514 p hg
    simpa only [d5847, d31, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d31, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5847, d31, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35516 (p : Pattern) (guard : d5854 p = 1) : d31 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35515 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35517 (p : Pattern) (guard : d8099 p = 1) : d31 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35516 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35518 (p : Pattern) (guard : d8105 p = 1) : d31 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35517 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35519 (p : Pattern) (guard : d8111 p = 1) : d53 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d53, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35518 p hg
    simpa only [d8111, d53, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d53, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5062 p hg
    simpa only [d8111, d53, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35520 (p : Pattern) (guard : d8112 p = 1) : d54 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d54, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35513 p hg
    simpa only [d8112, d54, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d54, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35519 p hg
    simpa only [d8112, d54, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35521 (p : Pattern) (guard : d5843 p = 1) : d4 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1199 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19859 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35522 (p : Pattern) (guard : d5847 p = 1) : d18 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d18, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35521 p hg
    simpa only [d5847, d18, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d18, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5847, d18, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35523 (p : Pattern) (guard : d5854 p = 1) : d18 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35522 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11461 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35524 (p : Pattern) (guard : d8099 p = 1) : d18 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35523 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11461 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35525 (p : Pattern) (guard : d8105 p = 1) : d18 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35524 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11461 p hg
    simpa only [d8105, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35526 (p : Pattern) (guard : d8111 p = 1) : d20 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d20, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35525 p hg
    simpa only [d8111, d20, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d20, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5050 p hg
    simpa only [d8111, d20, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35527 (p : Pattern) (guard : d8117 p = 1) : d55 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d55, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35526 p hg
    simpa only [d8117, d55, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d55, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34930 p hg
    simpa only [d8117, d55, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35528 (p : Pattern) (guard : d8118 p = 1) : d56 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d56, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35520 p hg
    simpa only [d8118, d56, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d56, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35527 p hg
    simpa only [d8118, d56, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35529 (p : Pattern) (guard : d8117 p = 1) : d61 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d61, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35491 p hg
    simpa only [d8117, d61, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d61, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d8117, d61, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35530 (p : Pattern) (guard : d8123 p = 1) : d64 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d64, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35529 p hg
    simpa only [d8123, d64, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d64, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d8123, d64, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35531 (p : Pattern) (guard : d8124 p = 1) : d65 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d65, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35528 p hg
    simpa only [d8124, d65, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d65, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35530 p hg
    simpa only [d8124, d65, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35532 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35533 (p : Pattern) (guard : d8117 p = 1) : d67 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35499 p hg
    simpa only [d8117, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35532 p hg
    simpa only [d8117, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35534 (p : Pattern) (guard : d0 p = 1) : d68 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare35535 (p : Pattern) (guard : d8123 p = 1) : d69 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35533 p hg
    simpa only [d8123, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35534 p hg
    simpa only [d8123, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35536 (p : Pattern) (guard : d8129 p = 1) : d75 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35535 p hg
    simpa only [d8129, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13494 p hg
    simpa only [d8129, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35537 (p : Pattern) (guard : d8130 p = 1) : d76 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d76, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35531 p hg
    simpa only [d8130, d76, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d76, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35536 p hg
    simpa only [d8130, d76, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35538 (p : Pattern) (guard : d8131 p = 1) : d77 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d77, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35508 p hg
    simpa only [d8131, d77, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d77, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35537 p hg
    simpa only [d8131, d77, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35539 (p : Pattern) (guard : d8111 p = 1) : d16 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35498 p hg
    simpa only [d8111, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5054 p hg
    simpa only [d8111, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35540 (p : Pattern) (guard : d8112 p = 1) : d16 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35454 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35539 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35541 (p : Pattern) (guard : d8117 p = 1) : d21 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35539 p hg
    simpa only [d8117, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3640 p hg
    simpa only [d8117, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35542 (p : Pattern) (guard : d8118 p = 1) : d22 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d22, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35540 p hg
    simpa only [d8118, d22, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d22, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35541 p hg
    simpa only [d8118, d22, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35543 (p : Pattern) (guard : d8123 p = 1) : d28 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35541 p hg
    simpa only [d8123, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4229 p hg
    simpa only [d8123, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35544 (p : Pattern) (guard : d8124 p = 1) : d29 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d29, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35542 p hg
    simpa only [d8124, d29, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d29, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35543 p hg
    simpa only [d8124, d29, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35545 (p : Pattern) (guard : d8117 p = 1) : d79 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34928 p hg
    simpa only [d8117, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3645 p hg
    simpa only [d8117, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35546 (p : Pattern) (guard : d8123 p = 1) : d80 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35545 p hg
    simpa only [d8123, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d8123, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35547 (p : Pattern) (guard : d8129 p = 1) : d81 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35546 p hg
    simpa only [d8129, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35548 (p : Pattern) (guard : d8130 p = 1) : d82 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d82, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35544 p hg
    simpa only [d8130, d82, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d82, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35547 p hg
    simpa only [d8130, d82, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35549 (p : Pattern) (guard : d5847 p = 1) : d14 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d14, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34145 p hg
    simpa only [d5847, d14, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d14, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d5847, d14, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35550 (p : Pattern) (guard : d5854 p = 1) : d14 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35549 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11458 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35551 (p : Pattern) (guard : d8099 p = 1) : d14 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35550 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11458 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35552 (p : Pattern) (guard : d8105 p = 1) : d14 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35551 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11458 p hg
    simpa only [d8105, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35553 (p : Pattern) (guard : d8111 p = 1) : d16 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d16, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35552 p hg
    simpa only [d8111, d16, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d16, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5054 p hg
    simpa only [d8111, d16, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35554 (p : Pattern) (guard : d8117 p = 1) : d54 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d54, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35553 p hg
    simpa only [d8117, d54, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d54, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8075 p hg
    simpa only [d8117, d54, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35555 (p : Pattern) (guard : d8123 p = 1) : d56 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d56, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35554 p hg
    simpa only [d8123, d56, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d56, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6474 p hg
    simpa only [d8123, d56, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35556 (p : Pattern) (guard : d8129 p = 1) : d65 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d65, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35555 p hg
    simpa only [d8129, d65, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d65, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3237 p hg
    simpa only [d8129, d65, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35557 (p : Pattern) (guard : d8135 p = 1) : d86 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d86, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35556 p hg
    simpa only [d8135, d86, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d86, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4600 p hg
    simpa only [d8135, d86, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35558 (p : Pattern) (guard : d8136 p = 1) : d87 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d87, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35548 p hg
    simpa only [d8136, d87, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d87, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35557 p hg
    simpa only [d8136, d87, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35559 (p : Pattern) (guard : d8137 p = 1) : d88 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d88, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35538 p hg
    simpa only [d8137, d88, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d88, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35558 p hg
    simpa only [d8137, d88, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
