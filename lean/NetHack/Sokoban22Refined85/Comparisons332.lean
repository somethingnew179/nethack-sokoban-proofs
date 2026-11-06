/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons331
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare46480 (p : Pattern) (guard : d8121 p = 1) : d2947 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d2947, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46445 p hg
    simpa only [d8121, d2947, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d2947, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46479 p hg
    simpa only [d8121, d2947, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46481 (p : Pattern) (guard : d8089 p = 1) : d2047 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38480 p hg
    simpa only [d8089, d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38707 p hg
    simpa only [d8089, d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46482 (p : Pattern) (guard : d8090 p = 1) : d2048 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38487 p hg
    simpa only [d8090, d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46481 p hg
    simpa only [d8090, d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46483 (p : Pattern) (guard : d8091 p = 1) : d2948 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2948, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34518 p hg
    simpa only [d8091, d2948, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2948, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46482 p hg
    simpa only [d8091, d2948, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46484 (p : Pattern) (guard : d8096 p = 1) : d2949 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2949, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46483 p hg
    simpa only [d8096, d2949, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2949, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38704 p hg
    simpa only [d8096, d2949, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46485 (p : Pattern) (guard : d5854 p = 1) : d2053 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d2053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38701 p hg
    simpa only [d5854, d2053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d2053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17502 p hg
    simpa only [d5854, d2053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46486 (p : Pattern) (guard : d8094 p = 1) : d2054 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38708 p hg
    simpa only [d8094, d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46485 p hg
    simpa only [d8094, d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46487 (p : Pattern) (guard : d8095 p = 1) : d2950 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2950, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34675 p hg
    simpa only [d8095, d2950, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2950, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46486 p hg
    simpa only [d8095, d2950, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46488 (p : Pattern) (guard : d8101 p = 1) : d2951 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2951, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46487 p hg
    simpa only [d8101, d2951, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2951, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38711 p hg
    simpa only [d8101, d2951, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46489 (p : Pattern) (guard : d8102 p = 1) : d2952 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2952, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46484 p hg
    simpa only [d8102, d2952, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2952, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46488 p hg
    simpa only [d8102, d2952, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46490 (p : Pattern) (guard : d8101 p = 1) : d2953 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46432 p hg
    simpa only [d8101, d2953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38716 p hg
    simpa only [d8101, d2953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46491 (p : Pattern) (guard : d8106 p = 1) : d2954 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46436 p hg
    simpa only [d8106, d2954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38721 p hg
    simpa only [d8106, d2954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46492 (p : Pattern) (guard : d8107 p = 1) : d2955 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46490 p hg
    simpa only [d8107, d2955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46491 p hg
    simpa only [d8107, d2955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46493 (p : Pattern) (guard : d8108 p = 1) : d2956 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2956, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46489 p hg
    simpa only [d8108, d2956, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2956, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46492 p hg
    simpa only [d8108, d2956, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46494 (p : Pattern) (guard : d8112 p = 1) : d2958 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46354 p hg
    simpa only [d8112, d2958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46495 (p : Pattern) (guard : d8113 p = 1) : d2959 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46492 p hg
    simpa only [d8113, d2959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46494 p hg
    simpa only [d8113, d2959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46496 (p : Pattern) (guard : d8114 p = 1) : d2960 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2960, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46493 p hg
    simpa only [d8114, d2960, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2960, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46495 p hg
    simpa only [d8114, d2960, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46497 (p : Pattern) (guard : d8095 p = 1) : d2935 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34474 p hg
    simpa only [d8095, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38550 p hg
    simpa only [d8095, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46498 (p : Pattern) (guard : d8101 p = 1) : d2961 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46497 p hg
    simpa only [d8101, d2961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38551 p hg
    simpa only [d8101, d2961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46499 (p : Pattern) (guard : d8100 p = 1) : d2962 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34568 p hg
    simpa only [d8100, d2962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38731 p hg
    simpa only [d8100, d2962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46500 (p : Pattern) (guard : d8106 p = 1) : d2963 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46499 p hg
    simpa only [d8106, d2963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38732 p hg
    simpa only [d8106, d2963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46501 (p : Pattern) (guard : d8107 p = 1) : d2964 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46498 p hg
    simpa only [d8107, d2964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46500 p hg
    simpa only [d8107, d2964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46502 (p : Pattern) (guard : d8113 p = 1) : d2965 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46501 p hg
    simpa only [d8113, d2965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46360 p hg
    simpa only [d8113, d2965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46503 (p : Pattern) (guard : d8119 p = 1) : d2966 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46502 p hg
    simpa only [d8119, d2966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d2966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46504 (p : Pattern) (guard : d8120 p = 1) : d2967 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2967, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46496 p hg
    simpa only [d8120, d2967, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2967, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46503 p hg
    simpa only [d8120, d2967, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46505 (p : Pattern) (guard : d8095 p = 1) : d2950 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2950, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34718 p hg
    simpa only [d8095, d2950, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2950, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46486 p hg
    simpa only [d8095, d2950, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46506 (p : Pattern) (guard : d8101 p = 1) : d2951 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2951, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46505 p hg
    simpa only [d8101, d2951, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2951, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38711 p hg
    simpa only [d8101, d2951, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46507 (p : Pattern) (guard : d8106 p = 1) : d2961 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46464 p hg
    simpa only [d8106, d2961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38742 p hg
    simpa only [d8106, d2961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46508 (p : Pattern) (guard : d8107 p = 1) : d2968 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2968, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46506 p hg
    simpa only [d8107, d2968, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2968, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46507 p hg
    simpa only [d8107, d2968, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46509 (p : Pattern) (guard : d8111 p = 1) : d2957 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46467 p hg
    simpa only [d8111, d2957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15337 p hg
    simpa only [d8111, d2957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46510 (p : Pattern) (guard : d8112 p = 1) : d2969 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46491 p hg
    simpa only [d8112, d2969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46509 p hg
    simpa only [d8112, d2969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46511 (p : Pattern) (guard : d8113 p = 1) : d2970 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2970, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46508 p hg
    simpa only [d8113, d2970, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2970, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46510 p hg
    simpa only [d8113, d2970, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46512 (p : Pattern) (guard : d8111 p = 1) : d2928 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46471 p hg
    simpa only [d8111, d2928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15307 p hg
    simpa only [d8111, d2928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46513 (p : Pattern) (guard : d8112 p = 1) : d2971 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46491 p hg
    simpa only [d8112, d2971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46512 p hg
    simpa only [d8112, d2971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46514 (p : Pattern) (guard : d8111 p = 1) : d2931 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46474 p hg
    simpa only [d8111, d2931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15286 p hg
    simpa only [d8111, d2931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46515 (p : Pattern) (guard : d8117 p = 1) : d2932 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46514 p hg
    simpa only [d8117, d2932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d2932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46516 (p : Pattern) (guard : d8118 p = 1) : d2972 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46513 p hg
    simpa only [d8118, d2972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46515 p hg
    simpa only [d8118, d2972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46517 (p : Pattern) (guard : d8119 p = 1) : d2973 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2973, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46511 p hg
    simpa only [d8119, d2973, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2973, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46516 p hg
    simpa only [d8119, d2973, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46518 (p : Pattern) (guard : d8112 p = 1) : d2974 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46500 p hg
    simpa only [d8112, d2974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d2974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46519 (p : Pattern) (guard : d8118 p = 1) : d2975 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46518 p hg
    simpa only [d8118, d2975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d2975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46520 (p : Pattern) (guard : d8124 p = 1) : d2976 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46519 p hg
    simpa only [d8124, d2976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d2976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46521 (p : Pattern) (guard : d8125 p = 1) : d2977 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2977, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46517 p hg
    simpa only [d8125, d2977, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2977, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46520 p hg
    simpa only [d8125, d2977, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46522 (p : Pattern) (guard : d8126 p = 1) : d2978 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2978, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46504 p hg
    simpa only [d8126, d2978, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2978, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46521 p hg
    simpa only [d8126, d2978, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46523 (p : Pattern) (guard : d8127 p = 1) : d2979 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d2979, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46480 p hg
    simpa only [d8127, d2979, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d2979, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46522 p hg
    simpa only [d8127, d2979, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46524 (p : Pattern) (guard : d8091 p = 1) : d2948 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2948, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34580 p hg
    simpa only [d8091, d2948, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2948, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46482 p hg
    simpa only [d8091, d2948, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46525 (p : Pattern) (guard : d8096 p = 1) : d2949 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2949, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46524 p hg
    simpa only [d8096, d2949, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2949, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38704 p hg
    simpa only [d8096, d2949, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46526 (p : Pattern) (guard : d8102 p = 1) : d2952 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2952, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46525 p hg
    simpa only [d8102, d2952, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2952, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46506 p hg
    simpa only [d8102, d2952, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46527 (p : Pattern) (guard : d8101 p = 1) : d2953 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2953, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46462 p hg
    simpa only [d8101, d2953, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2953, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38716 p hg
    simpa only [d8101, d2953, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46528 (p : Pattern) (guard : d8107 p = 1) : d2955 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2955, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46527 p hg
    simpa only [d8107, d2955, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2955, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46491 p hg
    simpa only [d8107, d2955, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46529 (p : Pattern) (guard : d8108 p = 1) : d2956 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2956, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46526 p hg
    simpa only [d8108, d2956, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2956, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46528 p hg
    simpa only [d8108, d2956, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46530 (p : Pattern) (guard : d8114 p = 1) : d2960 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2960, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46529 p hg
    simpa only [d8114, d2960, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2960, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46495 p hg
    simpa only [d8114, d2960, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46531 (p : Pattern) (guard : d8120 p = 1) : d2967 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2967, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46530 p hg
    simpa only [d8120, d2967, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2967, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46503 p hg
    simpa only [d8120, d2967, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46532 (p : Pattern) (guard : d8095 p = 1) : d2950 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2950, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34811 p hg
    simpa only [d8095, d2950, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2950, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46486 p hg
    simpa only [d8095, d2950, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46533 (p : Pattern) (guard : d8101 p = 1) : d2951 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2951, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46532 p hg
    simpa only [d8101, d2951, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2951, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38711 p hg
    simpa only [d8101, d2951, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46534 (p : Pattern) (guard : d8107 p = 1) : d2968 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2968, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46533 p hg
    simpa only [d8107, d2968, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2968, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46507 p hg
    simpa only [d8107, d2968, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46535 (p : Pattern) (guard : d8113 p = 1) : d2970 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2970, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46534 p hg
    simpa only [d8113, d2970, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2970, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46510 p hg
    simpa only [d8113, d2970, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46536 (p : Pattern) (guard : d8119 p = 1) : d2973 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2973, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46535 p hg
    simpa only [d8119, d2973, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2973, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46516 p hg
    simpa only [d8119, d2973, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46537 (p : Pattern) (guard : d8125 p = 1) : d2977 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2977, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46536 p hg
    simpa only [d8125, d2977, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2977, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46520 p hg
    simpa only [d8125, d2977, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46538 (p : Pattern) (guard : d8126 p = 1) : d2978 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2978, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46531 p hg
    simpa only [d8126, d2978, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2978, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46537 p hg
    simpa only [d8126, d2978, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46539 (p : Pattern) (guard : d8132 p = 1) : d2990 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d2990, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46538 p hg
    simpa only [d8132, d2990, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d2990, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d8132, d2990, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46540 (p : Pattern) (guard : d8133 p = 1) : d2991 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d2991, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46523 p hg
    simpa only [d8133, d2991, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d2991, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46539 p hg
    simpa only [d8133, d2991, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46541 (p : Pattern) (guard : d8134 p = 1) : d2992 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8128 p = 1 := by simpa only [d8134, d2992, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46409 p hg
    simpa only [d8134, d2992, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8133 p = 1 := by simpa only [d8134, d2992, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46540 p hg
    simpa only [d8134, d2992, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46542 (p : Pattern) (guard : d1 p = 1) : d1771 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1771, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34413 p hg
    simpa only [d1771, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1771, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38478 p hg
    simpa only [d1771, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46543 (p : Pattern) (guard : d8086 p = 1) : d1772 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d1772, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46542 p hg
    simpa only [d8086, d1772, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d1772, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38481 p hg
    simpa only [d8086, d1772, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46544 (p : Pattern) (guard : d8087 p = 1) : d2895 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d2895, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34746 p hg
    simpa only [d8087, d2895, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d2895, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46543 p hg
    simpa only [d8087, d2895, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46545 (p : Pattern) (guard : d8092 p = 1) : d2896 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d2896, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46544 p hg
    simpa only [d8092, d2896, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d2896, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38780 p hg
    simpa only [d8092, d2896, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46546 (p : Pattern) (guard : d8091 p = 1) : d2895 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2895, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34750 p hg
    simpa only [d8091, d2895, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2895, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38703 p hg
    simpa only [d8091, d2895, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46547 (p : Pattern) (guard : d8096 p = 1) : d2896 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2896, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46546 p hg
    simpa only [d8096, d2896, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2896, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38785 p hg
    simpa only [d8096, d2896, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46548 (p : Pattern) (guard : d8097 p = 1) : d2896 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46545 p hg
    simpa only [d8097, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46547 p hg
    simpa only [d8097, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46549 (p : Pattern) (guard : d8095 p = 1) : d2897 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2897, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34756 p hg
    simpa only [d8095, d2897, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2897, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46417 p hg
    simpa only [d8095, d2897, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46550 (p : Pattern) (guard : d8101 p = 1) : d2898 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2898, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46549 p hg
    simpa only [d8101, d2898, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2898, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38641 p hg
    simpa only [d8101, d2898, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46551 (p : Pattern) (guard : d8102 p = 1) : d2899 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2899, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46447 p hg
    simpa only [d8102, d2899, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2899, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46550 p hg
    simpa only [d8102, d2899, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46552 (p : Pattern) (guard : d8103 p = 1) : d2900 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d2900, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46548 p hg
    simpa only [d8103, d2900, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d2900, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46551 p hg
    simpa only [d8103, d2900, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46553 (p : Pattern) (guard : d8102 p = 1) : d2899 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2899, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46411 p hg
    simpa only [d8102, d2899, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2899, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46455 p hg
    simpa only [d8102, d2899, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46554 (p : Pattern) (guard : d8095 p = 1) : d2901 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2901, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34765 p hg
    simpa only [d8095, d2901, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2901, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38515 p hg
    simpa only [d8095, d2901, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46555 (p : Pattern) (guard : d8101 p = 1) : d2902 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2902, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46554 p hg
    simpa only [d8101, d2902, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2902, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38444 p hg
    simpa only [d8101, d2902, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46556 (p : Pattern) (guard : d8107 p = 1) : d2903 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2903, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46555 p hg
    simpa only [d8107, d2903, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2903, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d2903, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46557 (p : Pattern) (guard : d8108 p = 1) : d2904 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2904, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46553 p hg
    simpa only [d8108, d2904, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2904, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46556 p hg
    simpa only [d8108, d2904, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46558 (p : Pattern) (guard : d8109 p = 1) : d2905 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d2905, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46552 p hg
    simpa only [d8109, d2905, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d2905, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46557 p hg
    simpa only [d8109, d2905, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46559 (p : Pattern) (guard : d8091 p = 1) : d2906 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2906, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34580 p hg
    simpa only [d8091, d2906, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2906, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38498 p hg
    simpa only [d8091, d2906, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46560 (p : Pattern) (guard : d8096 p = 1) : d2907 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2907, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46559 p hg
    simpa only [d8096, d2907, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2907, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38527 p hg
    simpa only [d8096, d2907, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46561 (p : Pattern) (guard : d8095 p = 1) : d2906 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2906, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34718 p hg
    simpa only [d8095, d2906, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2906, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38715 p hg
    simpa only [d8095, d2906, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46562 (p : Pattern) (guard : d8101 p = 1) : d2908 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2908, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46561 p hg
    simpa only [d8101, d2908, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2908, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38534 p hg
    simpa only [d8101, d2908, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46563 (p : Pattern) (guard : d8102 p = 1) : d2909 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2909, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46560 p hg
    simpa only [d8102, d2909, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2909, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46562 p hg
    simpa only [d8102, d2909, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46564 (p : Pattern) (guard : d8101 p = 1) : d2910 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2910, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46462 p hg
    simpa only [d8101, d2910, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2910, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38457 p hg
    simpa only [d8101, d2910, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46565 (p : Pattern) (guard : d8107 p = 1) : d2913 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2913, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46564 p hg
    simpa only [d8107, d2913, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2913, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46437 p hg
    simpa only [d8107, d2913, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46566 (p : Pattern) (guard : d8108 p = 1) : d2914 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2914, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46563 p hg
    simpa only [d8108, d2914, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2914, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46565 p hg
    simpa only [d8108, d2914, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46567 (p : Pattern) (guard : d8114 p = 1) : d2920 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2920, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46566 p hg
    simpa only [d8114, d2920, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2920, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46443 p hg
    simpa only [d8114, d2920, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46568 (p : Pattern) (guard : d8115 p = 1) : d2921 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d2921, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46558 p hg
    simpa only [d8115, d2921, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d2921, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46567 p hg
    simpa only [d8115, d2921, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46569 (p : Pattern) (guard : d8091 p = 1) : d2895 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2895, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34779 p hg
    simpa only [d8091, d2895, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2895, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39054 p hg
    simpa only [d8091, d2895, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46570 (p : Pattern) (guard : d8096 p = 1) : d2896 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2896, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46569 p hg
    simpa only [d8096, d2896, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2896, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38810 p hg
    simpa only [d8096, d2896, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46571 (p : Pattern) (guard : d8095 p = 1) : d2922 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2922, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34786 p hg
    simpa only [d8095, d2922, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2922, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46450 p hg
    simpa only [d8095, d2922, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46572 (p : Pattern) (guard : d8101 p = 1) : d2923 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2923, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46571 p hg
    simpa only [d8101, d2923, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2923, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38671 p hg
    simpa only [d8101, d2923, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46573 (p : Pattern) (guard : d8102 p = 1) : d2924 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2924, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46570 p hg
    simpa only [d8102, d2924, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2924, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46572 p hg
    simpa only [d8102, d2924, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46574 (p : Pattern) (guard : d8095 p = 1) : d2897 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2897, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34791 p hg
    simpa only [d8095, d2897, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2897, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46417 p hg
    simpa only [d8095, d2897, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46575 (p : Pattern) (guard : d8101 p = 1) : d2898 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2898, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46574 p hg
    simpa only [d8101, d2898, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2898, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38641 p hg
    simpa only [d8101, d2898, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46576 (p : Pattern) (guard : d8100 p = 1) : d2901 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2901, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34796 p hg
    simpa only [d8100, d2901, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2901, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38557 p hg
    simpa only [d8100, d2901, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46577 (p : Pattern) (guard : d8106 p = 1) : d2902 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2902, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46576 p hg
    simpa only [d8106, d2902, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2902, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38678 p hg
    simpa only [d8106, d2902, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46578 (p : Pattern) (guard : d8107 p = 1) : d2925 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2925, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46575 p hg
    simpa only [d8107, d2925, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2925, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46577 p hg
    simpa only [d8107, d2925, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46579 (p : Pattern) (guard : d8108 p = 1) : d2926 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2926, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46573 p hg
    simpa only [d8108, d2926, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2926, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46578 p hg
    simpa only [d8108, d2926, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46580 (p : Pattern) (guard : d8100 p = 1) : d2927 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2927, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34804 p hg
    simpa only [d8100, d2927, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2927, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38563 p hg
    simpa only [d8100, d2927, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46581 (p : Pattern) (guard : d8106 p = 1) : d2928 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2928, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46580 p hg
    simpa only [d8106, d2928, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2928, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38564 p hg
    simpa only [d8106, d2928, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46582 (p : Pattern) (guard : d8107 p = 1) : d2929 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2929, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46550 p hg
    simpa only [d8107, d2929, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2929, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46581 p hg
    simpa only [d8107, d2929, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46583 (p : Pattern) (guard : d8113 p = 1) : d2933 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2933, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46582 p hg
    simpa only [d8113, d2933, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2933, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46360 p hg
    simpa only [d8113, d2933, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46584 (p : Pattern) (guard : d8114 p = 1) : d2934 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2934, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46579 p hg
    simpa only [d8114, d2934, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2934, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46583 p hg
    simpa only [d8114, d2934, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46585 (p : Pattern) (guard : d8095 p = 1) : d2906 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2906, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34811 p hg
    simpa only [d8095, d2906, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2906, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38715 p hg
    simpa only [d8095, d2906, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46586 (p : Pattern) (guard : d8101 p = 1) : d2908 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2908, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46585 p hg
    simpa only [d8101, d2908, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2908, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38534 p hg
    simpa only [d8101, d2908, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46587 (p : Pattern) (guard : d8107 p = 1) : d2937 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2937, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46586 p hg
    simpa only [d8107, d2937, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2937, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46465 p hg
    simpa only [d8107, d2937, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46588 (p : Pattern) (guard : d8113 p = 1) : d2939 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2939, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46587 p hg
    simpa only [d8113, d2939, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2939, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46469 p hg
    simpa only [d8113, d2939, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46589 (p : Pattern) (guard : d8119 p = 1) : d2945 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2945, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46588 p hg
    simpa only [d8119, d2945, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2945, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46477 p hg
    simpa only [d8119, d2945, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46590 (p : Pattern) (guard : d8120 p = 1) : d2946 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2946, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46584 p hg
    simpa only [d8120, d2946, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2946, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46589 p hg
    simpa only [d8120, d2946, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46591 (p : Pattern) (guard : d8121 p = 1) : d2947 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d2947, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46568 p hg
    simpa only [d8121, d2947, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d2947, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46590 p hg
    simpa only [d8121, d2947, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46592 (p : Pattern) (guard : d8091 p = 1) : d2948 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2948, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34620 p hg
    simpa only [d8091, d2948, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2948, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46482 p hg
    simpa only [d8091, d2948, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46593 (p : Pattern) (guard : d8096 p = 1) : d2949 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2949, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46592 p hg
    simpa only [d8096, d2949, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2949, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38704 p hg
    simpa only [d8096, d2949, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46594 (p : Pattern) (guard : d8102 p = 1) : d2952 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2952, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46593 p hg
    simpa only [d8102, d2952, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2952, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46533 p hg
    simpa only [d8102, d2952, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46595 (p : Pattern) (guard : d8101 p = 1) : d2953 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2953, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46561 p hg
    simpa only [d8101, d2953, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2953, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38716 p hg
    simpa only [d8101, d2953, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46596 (p : Pattern) (guard : d8107 p = 1) : d2955 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2955, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46595 p hg
    simpa only [d8107, d2955, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2955, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46491 p hg
    simpa only [d8107, d2955, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46597 (p : Pattern) (guard : d8108 p = 1) : d2956 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2956, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46594 p hg
    simpa only [d8108, d2956, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2956, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46596 p hg
    simpa only [d8108, d2956, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46598 (p : Pattern) (guard : d8113 p = 1) : d2959 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2959, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46528 p hg
    simpa only [d8113, d2959, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2959, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46494 p hg
    simpa only [d8113, d2959, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46599 (p : Pattern) (guard : d8114 p = 1) : d2960 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2960, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46597 p hg
    simpa only [d8114, d2960, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2960, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46598 p hg
    simpa only [d8114, d2960, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46600 (p : Pattern) (guard : d8120 p = 1) : d2967 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d2967, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46599 p hg
    simpa only [d8120, d2967, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d2967, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46503 p hg
    simpa only [d8120, d2967, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46601 (p : Pattern) (guard : d8095 p = 1) : d2950 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d2950, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34828 p hg
    simpa only [d8095, d2950, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d2950, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46486 p hg
    simpa only [d8095, d2950, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46602 (p : Pattern) (guard : d8101 p = 1) : d2951 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2951, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46601 p hg
    simpa only [d8101, d2951, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2951, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38711 p hg
    simpa only [d8101, d2951, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46603 (p : Pattern) (guard : d8100 p = 1) : d2935 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d2935, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34833 p hg
    simpa only [d8100, d2935, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d2935, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38741 p hg
    simpa only [d8100, d2935, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46604 (p : Pattern) (guard : d8106 p = 1) : d2961 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2961, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46603 p hg
    simpa only [d8106, d2961, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2961, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38742 p hg
    simpa only [d8106, d2961, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46605 (p : Pattern) (guard : d8107 p = 1) : d2968 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2968, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46602 p hg
    simpa only [d8107, d2968, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2968, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46604 p hg
    simpa only [d8107, d2968, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46606 (p : Pattern) (guard : d8113 p = 1) : d2970 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2970, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46605 p hg
    simpa only [d8113, d2970, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2970, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46510 p hg
    simpa only [d8113, d2970, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46607 (p : Pattern) (guard : d8119 p = 1) : d2973 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2973, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46606 p hg
    simpa only [d8119, d2973, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2973, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46516 p hg
    simpa only [d8119, d2973, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46608 (p : Pattern) (guard : d8125 p = 1) : d2977 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2977, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46607 p hg
    simpa only [d8125, d2977, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2977, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46520 p hg
    simpa only [d8125, d2977, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46609 (p : Pattern) (guard : d8126 p = 1) : d2978 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d2978, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46600 p hg
    simpa only [d8126, d2978, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d2978, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46608 p hg
    simpa only [d8126, d2978, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46610 (p : Pattern) (guard : d8127 p = 1) : d2979 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d2979, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46591 p hg
    simpa only [d8127, d2979, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d2979, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46609 p hg
    simpa only [d8127, d2979, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46611 (p : Pattern) (guard : d8091 p = 1) : d2948 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d2948, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34653 p hg
    simpa only [d8091, d2948, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d2948, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46482 p hg
    simpa only [d8091, d2948, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46612 (p : Pattern) (guard : d8096 p = 1) : d2949 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d2949, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46611 p hg
    simpa only [d8096, d2949, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d2949, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38704 p hg
    simpa only [d8096, d2949, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46613 (p : Pattern) (guard : d8102 p = 1) : d2952 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d2952, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46612 p hg
    simpa only [d8102, d2952, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d2952, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46602 p hg
    simpa only [d8102, d2952, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46614 (p : Pattern) (guard : d8101 p = 1) : d2953 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2953, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46585 p hg
    simpa only [d8101, d2953, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2953, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38716 p hg
    simpa only [d8101, d2953, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46615 (p : Pattern) (guard : d8107 p = 1) : d2955 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d2955, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46614 p hg
    simpa only [d8107, d2955, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d2955, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46491 p hg
    simpa only [d8107, d2955, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46616 (p : Pattern) (guard : d8108 p = 1) : d2956 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d2956, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46613 p hg
    simpa only [d8108, d2956, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d2956, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46615 p hg
    simpa only [d8108, d2956, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46617 (p : Pattern) (guard : d8113 p = 1) : d2959 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2959, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46596 p hg
    simpa only [d8113, d2959, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2959, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46494 p hg
    simpa only [d8113, d2959, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46618 (p : Pattern) (guard : d8114 p = 1) : d2960 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d2960, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46616 p hg
    simpa only [d8114, d2960, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d2960, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46617 p hg
    simpa only [d8114, d2960, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46619 (p : Pattern) (guard : d8101 p = 1) : d2961 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d2961, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46298 p hg
    simpa only [d8101, d2961, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d2961, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38551 p hg
    simpa only [d8101, d2961, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
