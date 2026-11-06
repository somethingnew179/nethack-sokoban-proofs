/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons245
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare34440 (p : Pattern) (guard : d5854 p = 1) : d18 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34363 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11461 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34441 (p : Pattern) (guard : d8094 p = 1) : d18 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34364 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34440 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34442 (p : Pattern) (guard : d8095 p = 1) : d18 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34365 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34441 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34443 (p : Pattern) (guard : d8100 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare34444 (p : Pattern) (guard : d8101 p = 1) : d43 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34442 p hg
    simpa only [d8101, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34445 (p : Pattern) (guard : d8102 p = 1) : d44 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d44, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34439 p hg
    simpa only [d8102, d44, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d44, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34444 p hg
    simpa only [d8102, d44, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34446 (p : Pattern) (guard : d8103 p = 1) : d45 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d45, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34429 p hg
    simpa only [d8103, d45, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d45, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34445 p hg
    simpa only [d8103, d45, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34447 (p : Pattern) (guard : d8091 p = 1) : d14 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34341 p hg
    simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34418 p hg
    simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34448 (p : Pattern) (guard : d8095 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare34449 (p : Pattern) (guard : d8096 p = 1) : d46 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d46, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34447 p hg
    simpa only [d8096, d46, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d46, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d8096, d46, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34450 (p : Pattern) (guard : d8102 p = 1) : d47 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d47, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34449 p hg
    simpa only [d8102, d47, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d47, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34444 p hg
    simpa only [d8102, d47, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34451 (p : Pattern) (guard : d5854 p = 1) : d24 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34393 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11467 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34452 (p : Pattern) (guard : d8094 p = 1) : d24 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34394 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34451 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34453 (p : Pattern) (guard : d8095 p = 1) : d24 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34395 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34452 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34454 (p : Pattern) (guard : d8101 p = 1) : d48 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34453 p hg
    simpa only [d8101, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34455 (p : Pattern) (guard : d8106 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare34456 (p : Pattern) (guard : d8107 p = 1) : d49 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34454 p hg
    simpa only [d8107, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34457 (p : Pattern) (guard : d8108 p = 1) : d50 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d50, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34450 p hg
    simpa only [d8108, d50, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d50, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34456 p hg
    simpa only [d8108, d50, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34458 (p : Pattern) (guard : d8109 p = 1) : d51 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d51, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34446 p hg
    simpa only [d8109, d51, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d51, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34457 p hg
    simpa only [d8109, d51, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34459 (p : Pattern) (guard : d8110 p = 1) : d52 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8104 p = 1 := by simpa only [d8110, d52, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34402 p hg
    simpa only [d8110, d52, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8109 p = 1 := by simpa only [d8110, d52, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34458 p hg
    simpa only [d8110, d52, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34460 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33815 p hg
    simpa only [d13, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d13, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34461 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d379 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33879 p hg
    simpa only [d14, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34460 p hg
    simpa only [d14, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34462 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d380 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34461 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34334 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34463 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d381 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34462 p hg
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34414 p hg
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34464 (p : Pattern) (guard : d8087 p = 1) : d14 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34463 p hg
    simpa only [d8087, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34343 p hg
    simpa only [d8087, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34465 (p : Pattern) (guard : d8091 p = 1) : d15 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d15, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34415 p hg
    simpa only [d8091, d15, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d15, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d15, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34466 (p : Pattern) (guard : d8092 p = 1) : d16 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d16, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34464 p hg
    simpa only [d8092, d16, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d16, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34465 p hg
    simpa only [d8092, d16, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34467 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare915 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34468 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34467 p hg
    simpa only [d31, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d31, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34469 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34468 p hg
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34470 (p : Pattern) (guard : d8086 p = 1) : d31 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34469 p hg
    simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34409 p hg
    simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34471 (p : Pattern) (guard : d5843 p = 1) : d2 p ≤ (0 : Int) + d12 p := by
  change (2 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34472 (p : Pattern) (guard : d5847 p = 1) : d31 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34471 p hg
    simpa only [d5847, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5847, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34473 (p : Pattern) (guard : d8089 p = 1) : d31 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34408 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34472 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34474 (p : Pattern) (guard : d8090 p = 1) : d31 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34409 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34473 p hg
    simpa only [d8090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34475 (p : Pattern) (guard : d8091 p = 1) : d31 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34470 p hg
    simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34474 p hg
    simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34476 (p : Pattern) (guard : d8095 p = 1) : d32 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34474 p hg
    simpa only [d8095, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34477 (p : Pattern) (guard : d8096 p = 1) : d53 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d53, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34475 p hg
    simpa only [d8096, d53, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d53, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34476 p hg
    simpa only [d8096, d53, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34478 (p : Pattern) (guard : d8097 p = 1) : d54 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d54, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34466 p hg
    simpa only [d8097, d54, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d54, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34477 p hg
    simpa only [d8097, d54, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34479 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare789 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34480 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34479 p hg
    simpa only [d18, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d18, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34481 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34480 p hg
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34482 (p : Pattern) (guard : d8086 p = 1) : d18 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34481 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34360 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34483 (p : Pattern) (guard : d8091 p = 1) : d18 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34482 p hg
    simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34365 p hg
    simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34484 (p : Pattern) (guard : d8096 p = 1) : d20 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d20, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34483 p hg
    simpa only [d8096, d20, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d20, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34368 p hg
    simpa only [d8096, d20, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34485 (p : Pattern) (guard : d8085 p = 1) : d24 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34386 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34389 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34486 (p : Pattern) (guard : d8090 p = 1) : d24 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34485 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34394 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34487 (p : Pattern) (guard : d8095 p = 1) : d24 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34486 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34452 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34488 (p : Pattern) (guard : d8099 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare34489 (p : Pattern) (guard : d8100 p = 1) : d25 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34452 p hg
    simpa only [d8100, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34490 (p : Pattern) (guard : d8101 p = 1) : d26 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d26, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34487 p hg
    simpa only [d8101, d26, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d26, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34489 p hg
    simpa only [d8101, d26, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34491 (p : Pattern) (guard : d8102 p = 1) : d55 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d55, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34484 p hg
    simpa only [d8102, d55, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d55, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34490 p hg
    simpa only [d8102, d55, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34492 (p : Pattern) (guard : d8103 p = 1) : d56 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d56, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34478 p hg
    simpa only [d8103, d56, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d56, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34491 p hg
    simpa only [d8103, d56, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34493 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14598 p hg
    simpa only [d58, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare814 p hg
    simpa only [d58, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34494 (p : Pattern) (guard : d5843 p = 1) : d57 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare813 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34495 (p : Pattern) (guard : d8084 p = 1) : d58 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare813 p hg
    simpa only [d8084, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34494 p hg
    simpa only [d8084, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34496 (p : Pattern) (guard : d8085 p = 1) : d58 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34493 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34495 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34497 (p : Pattern) (guard : d5843 p = 1) : d10 p ≤ (0 : Int) + d12 p := by
  change (10 : Int) ≤ (0 : Int) + 12
  decide
theorem compare34498 (p : Pattern) (guard : d5847 p = 1) : d58 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34497 p hg
    simpa only [d5847, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5847, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34499 (p : Pattern) (guard : d8089 p = 1) : d58 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34495 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34498 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34500 (p : Pattern) (guard : d8090 p = 1) : d58 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34496 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34499 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34501 (p : Pattern) (guard : d5854 p = 1) : d58 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34498 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11502 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34502 (p : Pattern) (guard : d8094 p = 1) : d58 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34499 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34501 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34503 (p : Pattern) (guard : d8095 p = 1) : d58 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34500 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34502 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34504 (p : Pattern) (guard : d8100 p = 1) : d59 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34502 p hg
    simpa only [d8100, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34505 (p : Pattern) (guard : d8101 p = 1) : d60 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d60, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34503 p hg
    simpa only [d8101, d60, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d60, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34504 p hg
    simpa only [d8101, d60, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34506 (p : Pattern) (guard : d8102 p = 1) : d61 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d61, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34369 p hg
    simpa only [d8102, d61, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d61, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34505 p hg
    simpa only [d8102, d61, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34507 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14576 p hg
    simpa only [d40, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare710 p hg
    simpa only [d40, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34508 (p : Pattern) (guard : d8085 p = 1) : d40 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34507 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34432 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34509 (p : Pattern) (guard : d8090 p = 1) : d40 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34508 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34436 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34510 (p : Pattern) (guard : d5854 p = 1) : d40 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34435 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11507 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34511 (p : Pattern) (guard : d8094 p = 1) : d40 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34436 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34510 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34512 (p : Pattern) (guard : d8095 p = 1) : d40 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34509 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34511 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34513 (p : Pattern) (guard : d8100 p = 1) : d41 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34511 p hg
    simpa only [d8100, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34514 (p : Pattern) (guard : d8101 p = 1) : d62 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d62, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34512 p hg
    simpa only [d8101, d62, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d62, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34513 p hg
    simpa only [d8101, d62, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34515 (p : Pattern) (guard : d8107 p = 1) : d63 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d63, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34514 p hg
    simpa only [d8107, d63, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d63, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d63, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34516 (p : Pattern) (guard : d8108 p = 1) : d64 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d64, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34506 p hg
    simpa only [d8108, d64, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d64, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34515 p hg
    simpa only [d8108, d64, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34517 (p : Pattern) (guard : d8109 p = 1) : d65 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d65, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34492 p hg
    simpa only [d8109, d65, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d65, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34516 p hg
    simpa only [d8109, d65, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34518 (p : Pattern) (guard : d8086 p = 1) : d14 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34324 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34340 p hg
    simpa only [d8086, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34519 (p : Pattern) (guard : d8091 p = 1) : d14 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34518 p hg
    simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34418 p hg
    simpa only [d8091, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34520 (p : Pattern) (guard : d8096 p = 1) : d37 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d37, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34519 p hg
    simpa only [d8096, d37, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d37, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34427 p hg
    simpa only [d8096, d37, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34521 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1532 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34522 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34521 p hg
    simpa only [d31, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d31, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34523 (p : Pattern) (guard : d8085 p = 1) : d31 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34522 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34408 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34524 (p : Pattern) (guard : d8090 p = 1) : d31 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34523 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34473 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34525 (p : Pattern) (guard : d5854 p = 1) : d31 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34472 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34526 (p : Pattern) (guard : d8094 p = 1) : d31 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34473 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34525 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34527 (p : Pattern) (guard : d8095 p = 1) : d31 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34524 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34526 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34528 (p : Pattern) (guard : d8101 p = 1) : d66 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d66, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34527 p hg
    simpa only [d8101, d66, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d66, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d66, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34529 (p : Pattern) (guard : d8102 p = 1) : d67 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d67, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34520 p hg
    simpa only [d8102, d67, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d67, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34528 p hg
    simpa only [d8102, d67, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34530 (p : Pattern) (guard : d8099 p = 1) : d24 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34451 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11467 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34531 (p : Pattern) (guard : d8100 p = 1) : d24 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34452 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34530 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34532 (p : Pattern) (guard : d8105 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare34533 (p : Pattern) (guard : d8106 p = 1) : d48 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34531 p hg
    simpa only [d8106, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34534 (p : Pattern) (guard : d8107 p = 1) : d68 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34444 p hg
    simpa only [d8107, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34533 p hg
    simpa only [d8107, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34535 (p : Pattern) (guard : d8108 p = 1) : d69 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d69, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34529 p hg
    simpa only [d8108, d69, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d69, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34534 p hg
    simpa only [d8108, d69, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34536 (p : Pattern) (guard : d8099 p = 1) : d58 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34501 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11502 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34537 (p : Pattern) (guard : d8100 p = 1) : d58 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34502 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34536 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34538 (p : Pattern) (guard : d8106 p = 1) : d70 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34537 p hg
    simpa only [d8106, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34539 (p : Pattern) (guard : d8107 p = 1) : d71 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34444 p hg
    simpa only [d8107, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34538 p hg
    simpa only [d8107, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34540 (p : Pattern) (guard : d8099 p = 1) : d40 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34510 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11507 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34541 (p : Pattern) (guard : d8100 p = 1) : d40 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34511 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34540 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34542 (p : Pattern) (guard : d8106 p = 1) : d72 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34541 p hg
    simpa only [d8106, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34543 (p : Pattern) (guard : d8111 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare34544 (p : Pattern) (guard : d8112 p = 1) : d73 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34542 p hg
    simpa only [d8112, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34545 (p : Pattern) (guard : d8113 p = 1) : d74 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34539 p hg
    simpa only [d8113, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34544 p hg
    simpa only [d8113, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34546 (p : Pattern) (guard : d8114 p = 1) : d75 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d75, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34535 p hg
    simpa only [d8114, d75, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d75, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34545 p hg
    simpa only [d8114, d75, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34547 (p : Pattern) (guard : d8115 p = 1) : d76 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d76, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34517 p hg
    simpa only [d8115, d76, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d76, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34546 p hg
    simpa only [d8115, d76, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34548 (p : Pattern) (guard : d8116 p = 1) : d77 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8110 p = 1 := by simpa only [d8116, d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34459 p hg
    simpa only [d8116, d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8115 p = 1 := by simpa only [d8116, d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34547 p hg
    simpa only [d8116, d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34549 (p : Pattern) (guard : d8095 p = 1) : d15 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34418 p hg
    simpa only [d8095, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34550 (p : Pattern) (guard : d8096 p = 1) : d16 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d16, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34519 p hg
    simpa only [d8096, d16, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d16, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34549 p hg
    simpa only [d8096, d16, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34551 (p : Pattern) (guard : d8097 p = 1) : d16 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34377 p hg
    simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34550 p hg
    simpa only [d8097, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34552 (p : Pattern) (guard : d8096 p = 1) : d16 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d16, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34419 p hg
    simpa only [d8096, d16, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d16, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34549 p hg
    simpa only [d8096, d16, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34553 (p : Pattern) (guard : d8100 p = 1) : d19 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34441 p hg
    simpa only [d8100, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34554 (p : Pattern) (guard : d8101 p = 1) : d20 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34442 p hg
    simpa only [d8101, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34553 p hg
    simpa only [d8101, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34555 (p : Pattern) (guard : d8102 p = 1) : d21 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d21, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34552 p hg
    simpa only [d8102, d21, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d21, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34554 p hg
    simpa only [d8102, d21, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34556 (p : Pattern) (guard : d8103 p = 1) : d22 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d22, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34551 p hg
    simpa only [d8103, d22, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d22, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34555 p hg
    simpa only [d8103, d22, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34557 (p : Pattern) (guard : d8096 p = 1) : d16 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d16, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34430 p hg
    simpa only [d8096, d16, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d16, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34549 p hg
    simpa only [d8096, d16, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34558 (p : Pattern) (guard : d8102 p = 1) : d21 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d21, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34557 p hg
    simpa only [d8102, d21, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d21, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34554 p hg
    simpa only [d8102, d21, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34559 (p : Pattern) (guard : d8101 p = 1) : d26 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34453 p hg
    simpa only [d8101, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34489 p hg
    simpa only [d8101, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34560 (p : Pattern) (guard : d8107 p = 1) : d27 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34559 p hg
    simpa only [d8107, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34561 (p : Pattern) (guard : d8108 p = 1) : d28 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d28, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34558 p hg
    simpa only [d8108, d28, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d28, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34560 p hg
    simpa only [d8108, d28, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34562 (p : Pattern) (guard : d8109 p = 1) : d29 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d29, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34556 p hg
    simpa only [d8109, d29, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d29, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34561 p hg
    simpa only [d8109, d29, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34563 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34522 p hg
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34564 (p : Pattern) (guard : d8086 p = 1) : d31 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34563 p hg
    simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34409 p hg
    simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34565 (p : Pattern) (guard : d8091 p = 1) : d31 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34564 p hg
    simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34474 p hg
    simpa only [d8091, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34566 (p : Pattern) (guard : d8096 p = 1) : d53 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d53, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34565 p hg
    simpa only [d8096, d53, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d53, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34476 p hg
    simpa only [d8096, d53, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34567 (p : Pattern) (guard : d5854 p = 1) : d35 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34424 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11542 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34568 (p : Pattern) (guard : d8094 p = 1) : d35 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34425 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34567 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34569 (p : Pattern) (guard : d8095 p = 1) : d35 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34426 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34568 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34570 (p : Pattern) (guard : d8100 p = 1) : d36 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34568 p hg
    simpa only [d8100, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34571 (p : Pattern) (guard : d8101 p = 1) : d78 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34569 p hg
    simpa only [d8101, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34570 p hg
    simpa only [d8101, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34572 (p : Pattern) (guard : d8102 p = 1) : d79 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d79, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34566 p hg
    simpa only [d8102, d79, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d79, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34571 p hg
    simpa only [d8102, d79, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34573 (p : Pattern) (guard : d8095 p = 1) : d40 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34437 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34511 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34574 (p : Pattern) (guard : d8101 p = 1) : d62 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34573 p hg
    simpa only [d8101, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34513 p hg
    simpa only [d8101, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34575 (p : Pattern) (guard : d8107 p = 1) : d63 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34574 p hg
    simpa only [d8107, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34576 (p : Pattern) (guard : d8108 p = 1) : d80 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d80, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34572 p hg
    simpa only [d8108, d80, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d80, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34575 p hg
    simpa only [d8108, d80, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34577 (p : Pattern) (guard : d8113 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare34578 (p : Pattern) (guard : d8114 p = 1) : d81 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d81, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34576 p hg
    simpa only [d8114, d81, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d81, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d81, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34579 (p : Pattern) (guard : d8115 p = 1) : d82 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d82, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34562 p hg
    simpa only [d8115, d82, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d82, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34578 p hg
    simpa only [d8115, d82, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
