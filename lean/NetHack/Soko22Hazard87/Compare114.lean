import NetHack.Soko22Hazard87.Compare113
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare28500 (p : Pattern) (guard : d2029 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28499 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28501 (p : Pattern) (guard : d2030 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28500 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28502 (p : Pattern) (guard : d2031 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28501 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28503 (p : Pattern) (guard : d2032 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2026 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28497 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28502 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28504 (p : Pattern) (guard : d2033 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2032 p = 1 := by simpa only [d2033, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28503 p hg
    simpa only [d2033, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2033, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d2033, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28505 (p : Pattern) (guard : d2034 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2012 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28483 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2033 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28504 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28506 (p : Pattern) (guard : d2035 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2034 p = 1 := by simpa only [d2035, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28505 p hg
    simpa only [d2035, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2035, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d2035, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28507 (p : Pattern) (guard : d2036 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2035 p = 1 := by simpa only [d2036, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28506 p hg
    simpa only [d2036, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2036, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d2036, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28508 (p : Pattern) (guard : d2037 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2037, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d2037, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2036 p = 1 := by simpa only [d2037, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28507 p hg
    simpa only [d2037, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28509 (p : Pattern) (guard : d2038 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2037 p = 1 := by simpa only [d2038, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28508 p hg
    simpa only [d2038, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2038, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d2038, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28510 (p : Pattern) (guard : d10363 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2033 p = 1 := by simpa only [d10363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28504 p hg
    simpa only [d10363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27421 p hg
    simpa only [d10363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28511 (p : Pattern) (guard : d10364 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10363 p = 1 := by simpa only [d10364, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28510 p hg
    simpa only [d10364, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10364, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d10364, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28512 (p : Pattern) (guard : d10366 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10364 p = 1 := by simpa only [d10366, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28511 p hg
    simpa only [d10366, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10366, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d10366, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28513 (p : Pattern) (guard : d17153 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17153, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d17153, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10366 p = 1 := by simpa only [d17153, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28512 p hg
    simpa only [d17153, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28514 (p : Pattern) (guard : d17154 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17153 p = 1 := by simpa only [d17154, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28513 p hg
    simpa only [d17154, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17154, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d17154, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28515 (p : Pattern) (guard : d17155 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2038 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28509 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17154 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28514 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28516 (p : Pattern) (guard : d10349 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2009 p = 1 := by simpa only [d10349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28480 p hg
    simpa only [d10349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d10349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28517 (p : Pattern) (guard : d10350 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10349 p = 1 := by simpa only [d10350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28516 p hg
    simpa only [d10350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d10350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28518 (p : Pattern) (guard : d10351 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10350 p = 1 := by simpa only [d10351, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28517 p hg
    simpa only [d10351, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10351, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d10351, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28519 (p : Pattern) (guard : d10352 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10351 p = 1 := by simpa only [d10352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28518 p hg
    simpa only [d10352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27421 p hg
    simpa only [d10352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28520 (p : Pattern) (guard : d10353 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10352 p = 1 := by simpa only [d10353, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28519 p hg
    simpa only [d10353, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10353, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d10353, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28521 (p : Pattern) (guard : d10355 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10353 p = 1 := by simpa only [d10355, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28520 p hg
    simpa only [d10355, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10355, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d10355, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28522 (p : Pattern) (guard : d13675 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13675, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d13675, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10355 p = 1 := by simpa only [d13675, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28521 p hg
    simpa only [d13675, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28523 (p : Pattern) (guard : d13676 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13675 p = 1 := by simpa only [d13676, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28522 p hg
    simpa only [d13676, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13676, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d13676, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28524 (p : Pattern) (guard : d5715 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28496 p hg
    simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28525 (p : Pattern) (guard : d5716 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5715 p = 1 := by simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28524 p hg
    simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28526 (p : Pattern) (guard : d5717 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5716 p = 1 := by simpa only [d5717, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28525 p hg
    simpa only [d5717, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5717, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d5717, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28527 (p : Pattern) (guard : d2046 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2027 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28498 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28528 (p : Pattern) (guard : d5238 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2046 p = 1 := by simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28527 p hg
    simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28529 (p : Pattern) (guard : d5239 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5238 p = 1 := by simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28528 p hg
    simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28530 (p : Pattern) (guard : d2047 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2046 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28527 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28531 (p : Pattern) (guard : d2048 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2047 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28530 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28532 (p : Pattern) (guard : d5243 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d5239 p = 1 := by simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28529 p hg
    simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28531 p hg
    simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28533 (p : Pattern) (guard : d2061 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2048 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28531 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28534 (p : Pattern) (guard : d5244 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5243 p = 1 := by simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28532 p hg
    simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28533 p hg
    simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28535 (p : Pattern) (guard : d5245 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5244 p = 1 := by simpa only [d5245, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28534 p hg
    simpa only [d5245, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5245, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d5245, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28536 (p : Pattern) (guard : d10370 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5717 p = 1 := by simpa only [d10370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28526 p hg
    simpa only [d10370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5245 p = 1 := by simpa only [d10370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28535 p hg
    simpa only [d10370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28537 (p : Pattern) (guard : d10371 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10370 p = 1 := by simpa only [d10371, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28536 p hg
    simpa only [d10371, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10371, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d10371, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28538 (p : Pattern) (guard : d10373 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10371 p = 1 := by simpa only [d10373, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28537 p hg
    simpa only [d10373, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10373, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d10373, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28539 (p : Pattern) (guard : d15548 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15548, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d15548, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10373 p = 1 := by simpa only [d15548, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28538 p hg
    simpa only [d15548, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28540 (p : Pattern) (guard : d15549 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15548 p = 1 := by simpa only [d15549, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28539 p hg
    simpa only [d15549, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15549, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d15549, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28541 (p : Pattern) (guard : d17156 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13676 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28523 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15549 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28540 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28542 (p : Pattern) (guard : d17157 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17155 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28515 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17156 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28541 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28543 (p : Pattern) (guard : d2039 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28485 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28498 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28544 (p : Pattern) (guard : d2040 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2018 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28489 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28545 (p : Pattern) (guard : d2041 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2039 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28543 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28544 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28546 (p : Pattern) (guard : d2042 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2022 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28493 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28547 (p : Pattern) (guard : d2043 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2042 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28546 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28548 (p : Pattern) (guard : d2044 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2041 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28545 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28547 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28549 (p : Pattern) (guard : d2045 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28496 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2044 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28548 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28550 (p : Pattern) (guard : d2049 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28501 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28531 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28551 (p : Pattern) (guard : d2050 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2045 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28549 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28550 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28552 (p : Pattern) (guard : d2051 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2050 p = 1 := by simpa only [d2051, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28551 p hg
    simpa only [d2051, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2051, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d2051, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28553 (p : Pattern) (guard : d2052 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2033 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28504 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2051 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28552 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28554 (p : Pattern) (guard : d2053 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2052 p = 1 := by simpa only [d2053, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28553 p hg
    simpa only [d2053, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2053, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d2053, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28555 (p : Pattern) (guard : d2054 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2053 p = 1 := by simpa only [d2054, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28554 p hg
    simpa only [d2054, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2054, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d2054, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28556 (p : Pattern) (guard : d2055 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2055, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d2055, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2055, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28555 p hg
    simpa only [d2055, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28557 (p : Pattern) (guard : d2056 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28556 p hg
    simpa only [d2056, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d2056, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28558 (p : Pattern) (guard : d10390 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2051 p = 1 := by simpa only [d10390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28552 p hg
    simpa only [d10390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5245 p = 1 := by simpa only [d10390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28535 p hg
    simpa only [d10390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28559 (p : Pattern) (guard : d10391 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10390 p = 1 := by simpa only [d10391, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28558 p hg
    simpa only [d10391, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10391, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d10391, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28560 (p : Pattern) (guard : d10393 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10391 p = 1 := by simpa only [d10393, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28559 p hg
    simpa only [d10393, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10393, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d10393, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28561 (p : Pattern) (guard : d17158 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17158, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d17158, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10393 p = 1 := by simpa only [d17158, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28560 p hg
    simpa only [d17158, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28562 (p : Pattern) (guard : d17159 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17158 p = 1 := by simpa only [d17159, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28561 p hg
    simpa only [d17159, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17159, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d17159, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28563 (p : Pattern) (guard : d17160 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2056 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28557 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17159 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28562 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28564 (p : Pattern) (guard : d15550 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15549 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28540 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28565 (p : Pattern) (guard : d17161 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17160 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28563 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15550 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28564 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28566 (p : Pattern) (guard : d17162 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17157 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28542 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17161 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28565 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28567 (p : Pattern) (guard : d17163 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17163, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d17163, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17162 p = 1 := by simpa only [d17163, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28566 p hg
    simpa only [d17163, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28568 (p : Pattern) (guard : d17164 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17164, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d17164, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17163 p = 1 := by simpa only [d17164, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28567 p hg
    simpa only [d17164, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28569 (p : Pattern) (guard : d5240 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28496 p hg
    simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5239 p = 1 := by simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28529 p hg
    simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28570 (p : Pattern) (guard : d5241 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5240 p = 1 := by simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28569 p hg
    simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28550 p hg
    simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28571 (p : Pattern) (guard : d5242 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5241 p = 1 := by simpa only [d5242, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28570 p hg
    simpa only [d5242, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5242, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d5242, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28572 (p : Pattern) (guard : d5246 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5242 p = 1 := by simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28571 p hg
    simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5245 p = 1 := by simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28535 p hg
    simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28573 (p : Pattern) (guard : d5247 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5246 p = 1 := by simpa only [d5247, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28572 p hg
    simpa only [d5247, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5247, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d5247, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28574 (p : Pattern) (guard : d5248 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5247 p = 1 := by simpa only [d5248, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28573 p hg
    simpa only [d5248, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5248, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d5248, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28575 (p : Pattern) (guard : d5249 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5249, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d5249, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5248 p = 1 := by simpa only [d5249, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28574 p hg
    simpa only [d5249, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28576 (p : Pattern) (guard : d5250 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5249 p = 1 := by simpa only [d5250, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28575 p hg
    simpa only [d5250, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5250, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d5250, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28577 (p : Pattern) (guard : d5251 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5250 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28576 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28578 (p : Pattern) (guard : d2058 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28544 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28579 (p : Pattern) (guard : d2059 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2058 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28578 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28547 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28580 (p : Pattern) (guard : d2076 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28579 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28581 (p : Pattern) (guard : d10405 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2040 p = 1 := by simpa only [d10405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28544 p hg
    simpa only [d10405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d10405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28582 (p : Pattern) (guard : d10406 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2042 p = 1 := by simpa only [d10406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28546 p hg
    simpa only [d10406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d10406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28583 (p : Pattern) (guard : d10407 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10405 p = 1 := by simpa only [d10407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28581 p hg
    simpa only [d10407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10406 p = 1 := by simpa only [d10407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28582 p hg
    simpa only [d10407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28584 (p : Pattern) (guard : d10408 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d10407 p = 1 := by simpa only [d10408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28583 p hg
    simpa only [d10408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d10408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28585 (p : Pattern) (guard : d10409 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2076 p = 1 := by simpa only [d10409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28580 p hg
    simpa only [d10409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10408 p = 1 := by simpa only [d10409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28584 p hg
    simpa only [d10409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28586 (p : Pattern) (guard : d10410 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10409 p = 1 := by simpa only [d10410, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28585 p hg
    simpa only [d10410, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10410, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d10410, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28587 (p : Pattern) (guard : d10411 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10410 p = 1 := by simpa only [d10411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28586 p hg
    simpa only [d10411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27421 p hg
    simpa only [d10411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28588 (p : Pattern) (guard : d10412 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10411 p = 1 := by simpa only [d10412, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28587 p hg
    simpa only [d10412, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10412, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d10412, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28589 (p : Pattern) (guard : d10414 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10412 p = 1 := by simpa only [d10414, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28588 p hg
    simpa only [d10414, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10414, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d10414, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28590 (p : Pattern) (guard : d15555 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15555, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d15555, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10414 p = 1 := by simpa only [d15555, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28589 p hg
    simpa only [d15555, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28591 (p : Pattern) (guard : d15556 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15555 p = 1 := by simpa only [d15556, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28590 p hg
    simpa only [d15556, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15556, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d15556, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28592 (p : Pattern) (guard : d15557 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15556 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28591 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28593 (p : Pattern) (guard : d15558 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5251 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28577 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28592 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28594 (p : Pattern) (guard : d17165 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28565 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15558 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28593 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28595 (p : Pattern) (guard : d17166 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17166, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d17166, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17165 p = 1 := by simpa only [d17166, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28594 p hg
    simpa only [d17166, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28596 (p : Pattern) (guard : d17167 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17167, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d17167, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17166 p = 1 := by simpa only [d17167, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28595 p hg
    simpa only [d17167, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28597 (p : Pattern) (guard : d17168 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17164 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28568 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17167 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28596 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28598 (p : Pattern) (guard : d2060 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28579 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28531 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28599 (p : Pattern) (guard : d2062 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2060 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28598 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28533 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28600 (p : Pattern) (guard : d2063 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2062 p = 1 := by simpa only [d2063, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28599 p hg
    simpa only [d2063, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2063, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d2063, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28601 (p : Pattern) (guard : d2064 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2051 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28552 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2063 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28600 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28602 (p : Pattern) (guard : d2065 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2064 p = 1 := by simpa only [d2065, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28601 p hg
    simpa only [d2065, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2065, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d2065, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28603 (p : Pattern) (guard : d2066 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2065 p = 1 := by simpa only [d2066, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28602 p hg
    simpa only [d2066, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2066, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d2066, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28604 (p : Pattern) (guard : d2067 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2067, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d2067, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2067, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28603 p hg
    simpa only [d2067, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28605 (p : Pattern) (guard : d2068 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28604 p hg
    simpa only [d2068, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d2068, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28606 (p : Pattern) (guard : d2071 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2068 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28605 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28607 (p : Pattern) (guard : d15563 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28606 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28592 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28608 (p : Pattern) (guard : d17169 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28565 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15563 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28607 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28609 (p : Pattern) (guard : d17170 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17170, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d17170, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17169 p = 1 := by simpa only [d17170, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28608 p hg
    simpa only [d17170, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28610 (p : Pattern) (guard : d17171 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17171, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d17171, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17170 p = 1 := by simpa only [d17171, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28609 p hg
    simpa only [d17171, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28611 (p : Pattern) (guard : d17172 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17171 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28610 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28612 (p : Pattern) (guard : d17173 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28597 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17172 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28611 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28613 (p : Pattern) (guard : d1997 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27601 p hg
    simpa only [d1997, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27441 p hg
    simpa only [d1997, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28614 (p : Pattern) (guard : d1998 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28613 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28615 (p : Pattern) (guard : d1999 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28614 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28616 (p : Pattern) (guard : d2000 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28615 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28617 (p : Pattern) (guard : d2001 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1523 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28281 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28618 (p : Pattern) (guard : d2002 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2001 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28617 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28619 (p : Pattern) (guard : d2003 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2002 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28618 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28620 (p : Pattern) (guard : d2004 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28616 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2003 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28619 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28621 (p : Pattern) (guard : d2007 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28320 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28622 (p : Pattern) (guard : d2008 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2007 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28621 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28623 (p : Pattern) (guard : d2009 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2004 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28620 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2008 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28622 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28624 (p : Pattern) (guard : d2010 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2009 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28623 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28625 (p : Pattern) (guard : d2011 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2010 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28624 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28626 (p : Pattern) (guard : d2012 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2011 p = 1 := by simpa only [d2012, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28625 p hg
    simpa only [d2012, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2012, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d2012, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28627 (p : Pattern) (guard : d2013 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28613 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28628 (p : Pattern) (guard : d2014 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28614 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28627 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28629 (p : Pattern) (guard : d2015 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1999 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28615 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28628 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28630 (p : Pattern) (guard : d2016 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d2016, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27519 p hg
    simpa only [d2016, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2016, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27441 p hg
    simpa only [d2016, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28631 (p : Pattern) (guard : d2017 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28613 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2016 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28630 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28632 (p : Pattern) (guard : d2018 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2017 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28631 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28633 (p : Pattern) (guard : d2019 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28618 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2018 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28632 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28634 (p : Pattern) (guard : d2020 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2015 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28629 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2019 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28633 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28635 (p : Pattern) (guard : d2021 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d2016 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28630 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28636 (p : Pattern) (guard : d2022 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2021 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28635 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28637 (p : Pattern) (guard : d2023 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28320 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2022 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28636 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28638 (p : Pattern) (guard : d2024 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2023 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28637 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28639 (p : Pattern) (guard : d2025 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2020 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28634 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2024 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28638 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28640 (p : Pattern) (guard : d2026 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2009 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28623 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2025 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28639 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28641 (p : Pattern) (guard : d2027 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28627 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28642 (p : Pattern) (guard : d2028 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28641 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28643 (p : Pattern) (guard : d2029 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28642 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28644 (p : Pattern) (guard : d2030 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28643 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28645 (p : Pattern) (guard : d2031 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28644 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28646 (p : Pattern) (guard : d2032 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2026 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28640 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28645 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28647 (p : Pattern) (guard : d2033 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2032 p = 1 := by simpa only [d2033, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28646 p hg
    simpa only [d2033, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2033, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d2033, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28648 (p : Pattern) (guard : d2034 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2012 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28626 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2033 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28647 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28649 (p : Pattern) (guard : d2035 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2034 p = 1 := by simpa only [d2035, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28648 p hg
    simpa only [d2035, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2035, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d2035, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28650 (p : Pattern) (guard : d2036 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2035 p = 1 := by simpa only [d2036, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28649 p hg
    simpa only [d2036, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2036, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d2036, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28651 (p : Pattern) (guard : d2037 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2037, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d2037, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2036 p = 1 := by simpa only [d2037, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28650 p hg
    simpa only [d2037, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28652 (p : Pattern) (guard : d2038 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2037 p = 1 := by simpa only [d2038, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28651 p hg
    simpa only [d2038, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2038, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d2038, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28653 (p : Pattern) (guard : d10363 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2033 p = 1 := by simpa only [d10363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28647 p hg
    simpa only [d10363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27453 p hg
    simpa only [d10363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28654 (p : Pattern) (guard : d10364 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10363 p = 1 := by simpa only [d10364, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28653 p hg
    simpa only [d10364, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10364, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d10364, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28655 (p : Pattern) (guard : d10366 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10364 p = 1 := by simpa only [d10366, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28654 p hg
    simpa only [d10366, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10366, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d10366, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28656 (p : Pattern) (guard : d17153 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17153, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d17153, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10366 p = 1 := by simpa only [d17153, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28655 p hg
    simpa only [d17153, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28657 (p : Pattern) (guard : d17154 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17153 p = 1 := by simpa only [d17154, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28656 p hg
    simpa only [d17154, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17154, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d17154, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28658 (p : Pattern) (guard : d17155 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2038 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28652 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17154 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28657 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28659 (p : Pattern) (guard : d10349 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2009 p = 1 := by simpa only [d10349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28623 p hg
    simpa only [d10349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d10349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28660 (p : Pattern) (guard : d10350 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10349 p = 1 := by simpa only [d10350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28659 p hg
    simpa only [d10350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d10350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28661 (p : Pattern) (guard : d10351 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10350 p = 1 := by simpa only [d10351, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28660 p hg
    simpa only [d10351, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10351, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d10351, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28662 (p : Pattern) (guard : d10352 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10351 p = 1 := by simpa only [d10352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28661 p hg
    simpa only [d10352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27453 p hg
    simpa only [d10352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28663 (p : Pattern) (guard : d10353 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10352 p = 1 := by simpa only [d10353, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28662 p hg
    simpa only [d10353, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10353, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d10353, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28664 (p : Pattern) (guard : d10355 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10353 p = 1 := by simpa only [d10355, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28663 p hg
    simpa only [d10355, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10355, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d10355, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28665 (p : Pattern) (guard : d13675 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13675, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d13675, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10355 p = 1 := by simpa only [d13675, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28664 p hg
    simpa only [d13675, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28666 (p : Pattern) (guard : d13676 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13675 p = 1 := by simpa only [d13676, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28665 p hg
    simpa only [d13676, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13676, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d13676, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28667 (p : Pattern) (guard : d5715 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28639 p hg
    simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28668 (p : Pattern) (guard : d5716 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5715 p = 1 := by simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28667 p hg
    simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28669 (p : Pattern) (guard : d5717 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5716 p = 1 := by simpa only [d5717, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28668 p hg
    simpa only [d5717, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5717, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d5717, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28670 (p : Pattern) (guard : d2046 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2027 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28641 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28671 (p : Pattern) (guard : d5238 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2046 p = 1 := by simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28670 p hg
    simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28672 (p : Pattern) (guard : d5239 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5238 p = 1 := by simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28671 p hg
    simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28673 (p : Pattern) (guard : d2047 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2046 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28670 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28674 (p : Pattern) (guard : d2048 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2047 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28673 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28675 (p : Pattern) (guard : d5243 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d5239 p = 1 := by simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28672 p hg
    simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28674 p hg
    simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28676 (p : Pattern) (guard : d2061 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2048 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28674 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28677 (p : Pattern) (guard : d5244 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5243 p = 1 := by simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28675 p hg
    simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28676 p hg
    simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28678 (p : Pattern) (guard : d5245 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5244 p = 1 := by simpa only [d5245, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28677 p hg
    simpa only [d5245, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5245, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d5245, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28679 (p : Pattern) (guard : d10370 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5717 p = 1 := by simpa only [d10370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28669 p hg
    simpa only [d10370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5245 p = 1 := by simpa only [d10370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28678 p hg
    simpa only [d10370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28680 (p : Pattern) (guard : d10371 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10370 p = 1 := by simpa only [d10371, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28679 p hg
    simpa only [d10371, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10371, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d10371, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28681 (p : Pattern) (guard : d10373 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10371 p = 1 := by simpa only [d10373, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28680 p hg
    simpa only [d10373, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10373, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d10373, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28682 (p : Pattern) (guard : d15548 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15548, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d15548, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10373 p = 1 := by simpa only [d15548, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28681 p hg
    simpa only [d15548, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28683 (p : Pattern) (guard : d15549 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15548 p = 1 := by simpa only [d15549, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28682 p hg
    simpa only [d15549, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15549, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d15549, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28684 (p : Pattern) (guard : d17156 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13676 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28666 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15549 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28683 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28685 (p : Pattern) (guard : d17157 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17155 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28658 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17156 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28684 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28686 (p : Pattern) (guard : d2039 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28628 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28641 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28687 (p : Pattern) (guard : d2040 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2018 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28632 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28688 (p : Pattern) (guard : d2041 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2039 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28686 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28687 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28689 (p : Pattern) (guard : d2042 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2022 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28636 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28690 (p : Pattern) (guard : d2043 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2042 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28689 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28691 (p : Pattern) (guard : d2044 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2041 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28688 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28690 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28692 (p : Pattern) (guard : d2045 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28639 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2044 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28691 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28693 (p : Pattern) (guard : d2049 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28644 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28674 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28694 (p : Pattern) (guard : d2050 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2045 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28692 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28693 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28695 (p : Pattern) (guard : d2051 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2050 p = 1 := by simpa only [d2051, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28694 p hg
    simpa only [d2051, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2051, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d2051, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28696 (p : Pattern) (guard : d2052 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2033 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28647 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2051 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28695 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28697 (p : Pattern) (guard : d2053 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2052 p = 1 := by simpa only [d2053, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28696 p hg
    simpa only [d2053, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2053, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d2053, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28698 (p : Pattern) (guard : d2054 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2053 p = 1 := by simpa only [d2054, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28697 p hg
    simpa only [d2054, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2054, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d2054, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28699 (p : Pattern) (guard : d2055 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2055, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d2055, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2055, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28698 p hg
    simpa only [d2055, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28700 (p : Pattern) (guard : d2056 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28699 p hg
    simpa only [d2056, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d2056, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28701 (p : Pattern) (guard : d10390 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2051 p = 1 := by simpa only [d10390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28695 p hg
    simpa only [d10390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5245 p = 1 := by simpa only [d10390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28678 p hg
    simpa only [d10390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28702 (p : Pattern) (guard : d10391 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10390 p = 1 := by simpa only [d10391, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28701 p hg
    simpa only [d10391, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10391, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d10391, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28703 (p : Pattern) (guard : d10393 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10391 p = 1 := by simpa only [d10393, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28702 p hg
    simpa only [d10393, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10393, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d10393, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28704 (p : Pattern) (guard : d17158 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17158, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d17158, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10393 p = 1 := by simpa only [d17158, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28703 p hg
    simpa only [d17158, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28705 (p : Pattern) (guard : d17159 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17158 p = 1 := by simpa only [d17159, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28704 p hg
    simpa only [d17159, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17159, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d17159, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28706 (p : Pattern) (guard : d17160 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2056 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28700 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17159 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28705 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28707 (p : Pattern) (guard : d15550 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15549 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28683 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28708 (p : Pattern) (guard : d17161 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17160 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28706 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15550 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28707 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28709 (p : Pattern) (guard : d17162 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17157 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28685 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17161 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28708 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28710 (p : Pattern) (guard : d19525 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d17162 p = 1 := by simpa only [d19525, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28709 p hg
    simpa only [d19525, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19525, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d19525, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28711 (p : Pattern) (guard : d19526 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19526, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d19526, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19525 p = 1 := by simpa only [d19526, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28710 p hg
    simpa only [d19526, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28712 (p : Pattern) (guard : d5240 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28639 p hg
    simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5239 p = 1 := by simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28672 p hg
    simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28713 (p : Pattern) (guard : d5241 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5240 p = 1 := by simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28712 p hg
    simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28693 p hg
    simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28714 (p : Pattern) (guard : d5242 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5241 p = 1 := by simpa only [d5242, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28713 p hg
    simpa only [d5242, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5242, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d5242, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28715 (p : Pattern) (guard : d5246 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5242 p = 1 := by simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28714 p hg
    simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5245 p = 1 := by simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28678 p hg
    simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28716 (p : Pattern) (guard : d5247 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5246 p = 1 := by simpa only [d5247, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28715 p hg
    simpa only [d5247, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5247, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d5247, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28717 (p : Pattern) (guard : d5248 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5247 p = 1 := by simpa only [d5248, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28716 p hg
    simpa only [d5248, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5248, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d5248, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28718 (p : Pattern) (guard : d5249 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5249, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d5249, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5248 p = 1 := by simpa only [d5249, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28717 p hg
    simpa only [d5249, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28719 (p : Pattern) (guard : d5250 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5249 p = 1 := by simpa only [d5250, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28718 p hg
    simpa only [d5250, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5250, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d5250, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28720 (p : Pattern) (guard : d5251 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5250 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28719 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28721 (p : Pattern) (guard : d2058 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28687 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28722 (p : Pattern) (guard : d2059 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2058 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28721 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28690 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28723 (p : Pattern) (guard : d2076 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28722 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28724 (p : Pattern) (guard : d10405 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2040 p = 1 := by simpa only [d10405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28687 p hg
    simpa only [d10405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d10405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28725 (p : Pattern) (guard : d10406 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2042 p = 1 := by simpa only [d10406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28689 p hg
    simpa only [d10406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d10406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28726 (p : Pattern) (guard : d10407 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10405 p = 1 := by simpa only [d10407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28724 p hg
    simpa only [d10407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10406 p = 1 := by simpa only [d10407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28725 p hg
    simpa only [d10407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28727 (p : Pattern) (guard : d10408 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d10407 p = 1 := by simpa only [d10408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28726 p hg
    simpa only [d10408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d10408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28728 (p : Pattern) (guard : d10409 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2076 p = 1 := by simpa only [d10409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28723 p hg
    simpa only [d10409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10408 p = 1 := by simpa only [d10409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28727 p hg
    simpa only [d10409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28729 (p : Pattern) (guard : d10410 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10409 p = 1 := by simpa only [d10410, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28728 p hg
    simpa only [d10410, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10410, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d10410, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28730 (p : Pattern) (guard : d10411 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10410 p = 1 := by simpa only [d10411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28729 p hg
    simpa only [d10411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27453 p hg
    simpa only [d10411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28731 (p : Pattern) (guard : d10412 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10411 p = 1 := by simpa only [d10412, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28730 p hg
    simpa only [d10412, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10412, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d10412, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28732 (p : Pattern) (guard : d10414 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10412 p = 1 := by simpa only [d10414, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28731 p hg
    simpa only [d10414, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10414, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d10414, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28733 (p : Pattern) (guard : d15555 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15555, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d15555, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10414 p = 1 := by simpa only [d15555, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28732 p hg
    simpa only [d15555, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28734 (p : Pattern) (guard : d15556 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15555 p = 1 := by simpa only [d15556, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28733 p hg
    simpa only [d15556, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15556, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d15556, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28735 (p : Pattern) (guard : d15557 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15556 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28734 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28736 (p : Pattern) (guard : d15558 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5251 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28720 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28735 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28737 (p : Pattern) (guard : d17165 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28708 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15558 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28736 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28738 (p : Pattern) (guard : d19527 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d17165 p = 1 := by simpa only [d19527, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28737 p hg
    simpa only [d19527, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19527, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d19527, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28739 (p : Pattern) (guard : d19528 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19528, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d19528, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19527 p = 1 := by simpa only [d19528, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28738 p hg
    simpa only [d19528, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28740 (p : Pattern) (guard : d19529 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19526 p = 1 := by simpa only [d19529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28711 p hg
    simpa only [d19529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19528 p = 1 := by simpa only [d19529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28739 p hg
    simpa only [d19529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28741 (p : Pattern) (guard : d2060 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28722 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28674 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28742 (p : Pattern) (guard : d2062 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2060 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28741 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28676 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28743 (p : Pattern) (guard : d2063 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2062 p = 1 := by simpa only [d2063, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28742 p hg
    simpa only [d2063, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2063, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d2063, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28744 (p : Pattern) (guard : d2064 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2051 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28695 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2063 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28743 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28745 (p : Pattern) (guard : d2065 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2064 p = 1 := by simpa only [d2065, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28744 p hg
    simpa only [d2065, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2065, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d2065, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28746 (p : Pattern) (guard : d2066 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2065 p = 1 := by simpa only [d2066, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28745 p hg
    simpa only [d2066, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2066, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d2066, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28747 (p : Pattern) (guard : d2067 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2067, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d2067, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2067, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28746 p hg
    simpa only [d2067, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28748 (p : Pattern) (guard : d2068 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28747 p hg
    simpa only [d2068, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d2068, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28749 (p : Pattern) (guard : d2071 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2068 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28748 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
