import NetHack.Soko22Hazard87.Compare107
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare27000 (p : Pattern) (guard : d2028 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26999 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27001 (p : Pattern) (guard : d2029 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27000 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27002 (p : Pattern) (guard : d2030 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27001 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27003 (p : Pattern) (guard : d2031 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27002 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27004 (p : Pattern) (guard : d2032 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2026 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26998 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27003 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27005 (p : Pattern) (guard : d2033 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2032 p = 1 := by simpa only [d2033, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27004 p hg
    simpa only [d2033, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2033, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d2033, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27006 (p : Pattern) (guard : d2034 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2012 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26963 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2033 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27005 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27007 (p : Pattern) (guard : d2035 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2034 p = 1 := by simpa only [d2035, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27006 p hg
    simpa only [d2035, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2035, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d2035, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27008 (p : Pattern) (guard : d2036 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2035 p = 1 := by simpa only [d2036, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27007 p hg
    simpa only [d2036, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2036, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d2036, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27009 (p : Pattern) (guard : d2037 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2037, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d2037, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2036 p = 1 := by simpa only [d2037, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27008 p hg
    simpa only [d2037, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27010 (p : Pattern) (guard : d2038 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2037 p = 1 := by simpa only [d2038, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27009 p hg
    simpa only [d2038, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2038, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d2038, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27011 (p : Pattern) (guard : d10363 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2033 p = 1 := by simpa only [d10363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27005 p hg
    simpa only [d10363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25478 p hg
    simpa only [d10363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27012 (p : Pattern) (guard : d10364 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10363 p = 1 := by simpa only [d10364, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27011 p hg
    simpa only [d10364, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10364, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d10364, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27013 (p : Pattern) (guard : d10366 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10364 p = 1 := by simpa only [d10366, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27012 p hg
    simpa only [d10366, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10366, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d10366, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27014 (p : Pattern) (guard : d17153 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17153, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d17153, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10366 p = 1 := by simpa only [d17153, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27013 p hg
    simpa only [d17153, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27015 (p : Pattern) (guard : d17154 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17153 p = 1 := by simpa only [d17154, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27014 p hg
    simpa only [d17154, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17154, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d17154, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27016 (p : Pattern) (guard : d17155 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2038 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27010 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17154 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27015 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27017 (p : Pattern) (guard : d5715 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26997 p hg
    simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27018 (p : Pattern) (guard : d5716 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5715 p = 1 := by simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27017 p hg
    simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27019 (p : Pattern) (guard : d5717 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5716 p = 1 := by simpa only [d5717, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27018 p hg
    simpa only [d5717, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5717, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d5717, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27020 (p : Pattern) (guard : d2046 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2027 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26999 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27021 (p : Pattern) (guard : d5238 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2046 p = 1 := by simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27020 p hg
    simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27022 (p : Pattern) (guard : d5239 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5238 p = 1 := by simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27021 p hg
    simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27023 (p : Pattern) (guard : d2047 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2046 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27020 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27024 (p : Pattern) (guard : d2048 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2047 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27023 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27025 (p : Pattern) (guard : d5243 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d5239 p = 1 := by simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27022 p hg
    simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27024 p hg
    simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27026 (p : Pattern) (guard : d2061 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2048 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27024 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27027 (p : Pattern) (guard : d5244 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5243 p = 1 := by simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27025 p hg
    simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27026 p hg
    simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27028 (p : Pattern) (guard : d5245 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5244 p = 1 := by simpa only [d5245, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27027 p hg
    simpa only [d5245, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5245, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d5245, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27029 (p : Pattern) (guard : d10370 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5717 p = 1 := by simpa only [d10370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27019 p hg
    simpa only [d10370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5245 p = 1 := by simpa only [d10370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27028 p hg
    simpa only [d10370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27030 (p : Pattern) (guard : d10371 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10370 p = 1 := by simpa only [d10371, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27029 p hg
    simpa only [d10371, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10371, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d10371, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27031 (p : Pattern) (guard : d10373 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10371 p = 1 := by simpa only [d10373, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27030 p hg
    simpa only [d10373, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10373, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d10373, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27032 (p : Pattern) (guard : d15548 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15548, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d15548, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10373 p = 1 := by simpa only [d15548, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27031 p hg
    simpa only [d15548, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27033 (p : Pattern) (guard : d15549 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15548 p = 1 := by simpa only [d15549, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27032 p hg
    simpa only [d15549, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15549, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d15549, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27034 (p : Pattern) (guard : d17156 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13676 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26982 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15549 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27033 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27035 (p : Pattern) (guard : d17157 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17155 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27016 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17156 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27034 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27036 (p : Pattern) (guard : d17230 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17229 p = 1 := by simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26984 p hg
    simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17157 p = 1 := by simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27035 p hg
    simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27037 (p : Pattern) (guard : d17231 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17231, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d17231, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17230 p = 1 := by simpa only [d17231, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27036 p hg
    simpa only [d17231, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27038 (p : Pattern) (guard : d17232 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17232, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d17232, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17231 p = 1 := by simpa only [d17232, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27037 p hg
    simpa only [d17232, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27039 (p : Pattern) (guard : d15550 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15549 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27033 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27040 (p : Pattern) (guard : d17233 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17156 p = 1 := by simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27034 p hg
    simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15550 p = 1 := by simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27039 p hg
    simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27041 (p : Pattern) (guard : d17234 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17157 p = 1 := by simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27035 p hg
    simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17233 p = 1 := by simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27040 p hg
    simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27042 (p : Pattern) (guard : d17235 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17235, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d17235, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17234 p = 1 := by simpa only [d17235, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27041 p hg
    simpa only [d17235, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27043 (p : Pattern) (guard : d17236 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17236, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d17236, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17235 p = 1 := by simpa only [d17236, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27042 p hg
    simpa only [d17236, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27044 (p : Pattern) (guard : d17237 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17232 p = 1 := by simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27038 p hg
    simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17236 p = 1 := by simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27043 p hg
    simpa only [d17237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27045 (p : Pattern) (guard : d2039 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26986 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26999 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27046 (p : Pattern) (guard : d2040 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2018 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26990 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27047 (p : Pattern) (guard : d2041 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2039 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27045 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27046 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27048 (p : Pattern) (guard : d2042 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2022 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26994 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27049 (p : Pattern) (guard : d2043 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2042 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27048 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27050 (p : Pattern) (guard : d2044 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2041 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27047 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27049 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27051 (p : Pattern) (guard : d2045 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26997 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2044 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27050 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27052 (p : Pattern) (guard : d2049 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27002 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27024 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27053 (p : Pattern) (guard : d2050 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2045 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27051 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27052 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27054 (p : Pattern) (guard : d2051 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2050 p = 1 := by simpa only [d2051, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27053 p hg
    simpa only [d2051, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2051, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d2051, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27055 (p : Pattern) (guard : d2052 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2033 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27005 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2051 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27054 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27056 (p : Pattern) (guard : d2053 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2052 p = 1 := by simpa only [d2053, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27055 p hg
    simpa only [d2053, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2053, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d2053, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27057 (p : Pattern) (guard : d2054 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2053 p = 1 := by simpa only [d2054, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27056 p hg
    simpa only [d2054, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2054, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d2054, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27058 (p : Pattern) (guard : d2055 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2055, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d2055, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2055, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27057 p hg
    simpa only [d2055, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27059 (p : Pattern) (guard : d2056 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27058 p hg
    simpa only [d2056, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d2056, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27060 (p : Pattern) (guard : d10390 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2051 p = 1 := by simpa only [d10390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27054 p hg
    simpa only [d10390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5245 p = 1 := by simpa only [d10390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27028 p hg
    simpa only [d10390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27061 (p : Pattern) (guard : d10391 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10390 p = 1 := by simpa only [d10391, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27060 p hg
    simpa only [d10391, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10391, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d10391, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27062 (p : Pattern) (guard : d10393 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10391 p = 1 := by simpa only [d10393, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27061 p hg
    simpa only [d10393, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10393, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d10393, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27063 (p : Pattern) (guard : d17158 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17158, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d17158, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10393 p = 1 := by simpa only [d17158, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27062 p hg
    simpa only [d17158, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27064 (p : Pattern) (guard : d17159 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17158 p = 1 := by simpa only [d17159, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27063 p hg
    simpa only [d17159, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17159, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d17159, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27065 (p : Pattern) (guard : d17160 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2056 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27059 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17159 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27064 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27066 (p : Pattern) (guard : d17161 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17160 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27065 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15550 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27039 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27067 (p : Pattern) (guard : d17162 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17157 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27035 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17161 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27066 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27068 (p : Pattern) (guard : d17163 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17163, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d17163, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17162 p = 1 := by simpa only [d17163, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27067 p hg
    simpa only [d17163, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27069 (p : Pattern) (guard : d17164 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17164, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d17164, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17163 p = 1 := by simpa only [d17164, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27068 p hg
    simpa only [d17164, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27070 (p : Pattern) (guard : d5240 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26997 p hg
    simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5239 p = 1 := by simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27022 p hg
    simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27071 (p : Pattern) (guard : d5241 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5240 p = 1 := by simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27070 p hg
    simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27052 p hg
    simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27072 (p : Pattern) (guard : d5242 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5241 p = 1 := by simpa only [d5242, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27071 p hg
    simpa only [d5242, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5242, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d5242, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27073 (p : Pattern) (guard : d5246 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5242 p = 1 := by simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27072 p hg
    simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5245 p = 1 := by simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27028 p hg
    simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27074 (p : Pattern) (guard : d5247 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5246 p = 1 := by simpa only [d5247, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27073 p hg
    simpa only [d5247, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5247, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d5247, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27075 (p : Pattern) (guard : d5248 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5247 p = 1 := by simpa only [d5248, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27074 p hg
    simpa only [d5248, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5248, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d5248, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27076 (p : Pattern) (guard : d5249 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5249, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d5249, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5248 p = 1 := by simpa only [d5249, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27075 p hg
    simpa only [d5249, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27077 (p : Pattern) (guard : d5250 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5249 p = 1 := by simpa only [d5250, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27076 p hg
    simpa only [d5250, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5250, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d5250, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27078 (p : Pattern) (guard : d5251 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5250 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27077 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27079 (p : Pattern) (guard : d2058 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27046 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27080 (p : Pattern) (guard : d2059 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2058 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27079 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27049 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27081 (p : Pattern) (guard : d2076 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27080 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27082 (p : Pattern) (guard : d10405 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2040 p = 1 := by simpa only [d10405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27046 p hg
    simpa only [d10405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27083 (p : Pattern) (guard : d10406 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2042 p = 1 := by simpa only [d10406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27048 p hg
    simpa only [d10406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27084 (p : Pattern) (guard : d10407 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10405 p = 1 := by simpa only [d10407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27082 p hg
    simpa only [d10407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10406 p = 1 := by simpa only [d10407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27083 p hg
    simpa only [d10407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27085 (p : Pattern) (guard : d10408 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d10407 p = 1 := by simpa only [d10408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27084 p hg
    simpa only [d10408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d10408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27086 (p : Pattern) (guard : d10409 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2076 p = 1 := by simpa only [d10409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27081 p hg
    simpa only [d10409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10408 p = 1 := by simpa only [d10409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27085 p hg
    simpa only [d10409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27087 (p : Pattern) (guard : d10410 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10409 p = 1 := by simpa only [d10410, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27086 p hg
    simpa only [d10410, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10410, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d10410, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27088 (p : Pattern) (guard : d10411 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10410 p = 1 := by simpa only [d10411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27087 p hg
    simpa only [d10411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25478 p hg
    simpa only [d10411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27089 (p : Pattern) (guard : d10412 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10411 p = 1 := by simpa only [d10412, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27088 p hg
    simpa only [d10412, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10412, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d10412, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27090 (p : Pattern) (guard : d10414 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10412 p = 1 := by simpa only [d10414, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27089 p hg
    simpa only [d10414, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10414, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d10414, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27091 (p : Pattern) (guard : d15555 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15555, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d15555, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10414 p = 1 := by simpa only [d15555, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27090 p hg
    simpa only [d15555, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27092 (p : Pattern) (guard : d15556 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15555 p = 1 := by simpa only [d15556, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27091 p hg
    simpa only [d15556, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15556, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d15556, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27093 (p : Pattern) (guard : d15557 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15556 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27092 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27094 (p : Pattern) (guard : d15558 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5251 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27078 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27093 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27095 (p : Pattern) (guard : d17165 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27066 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15558 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27094 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27096 (p : Pattern) (guard : d17166 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17166, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d17166, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17165 p = 1 := by simpa only [d17166, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27095 p hg
    simpa only [d17166, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27097 (p : Pattern) (guard : d17167 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17167, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d17167, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17166 p = 1 := by simpa only [d17167, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27096 p hg
    simpa only [d17167, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27098 (p : Pattern) (guard : d17168 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17164 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27069 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17167 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27097 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27099 (p : Pattern) (guard : d17238 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17237 p = 1 := by simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27044 p hg
    simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17168 p = 1 := by simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27098 p hg
    simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27100 (p : Pattern) (guard : d1997 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25655 p hg
    simpa only [d1997, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25498 p hg
    simpa only [d1997, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27101 (p : Pattern) (guard : d1998 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27100 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27102 (p : Pattern) (guard : d1999 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27101 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27103 (p : Pattern) (guard : d2000 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27102 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27104 (p : Pattern) (guard : d2001 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1523 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26673 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27105 (p : Pattern) (guard : d2002 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2001 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27104 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27106 (p : Pattern) (guard : d2003 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2002 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27105 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27107 (p : Pattern) (guard : d2004 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27103 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2003 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27106 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27108 (p : Pattern) (guard : d2007 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26711 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27109 (p : Pattern) (guard : d2008 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2007 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27108 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27110 (p : Pattern) (guard : d2009 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2004 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27107 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2008 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27109 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27111 (p : Pattern) (guard : d2010 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2009 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27110 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27112 (p : Pattern) (guard : d2011 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2010 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27111 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27113 (p : Pattern) (guard : d2012 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2011 p = 1 := by simpa only [d2012, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27112 p hg
    simpa only [d2012, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2012, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d2012, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27114 (p : Pattern) (guard : d2143 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25510 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2012 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27113 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27115 (p : Pattern) (guard : d2144 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2143 p = 1 := by simpa only [d2144, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27114 p hg
    simpa only [d2144, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2144, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d2144, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27116 (p : Pattern) (guard : d2145 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2144 p = 1 := by simpa only [d2145, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27115 p hg
    simpa only [d2145, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2145, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d2145, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27117 (p : Pattern) (guard : d2146 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2146, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d2146, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2145 p = 1 := by simpa only [d2146, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27116 p hg
    simpa only [d2146, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27118 (p : Pattern) (guard : d2147 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2146 p = 1 := by simpa only [d2147, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27117 p hg
    simpa only [d2147, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2147, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d2147, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27119 (p : Pattern) (guard : d10342 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2012 p = 1 := by simpa only [d10342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27113 p hg
    simpa only [d10342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25510 p hg
    simpa only [d10342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27120 (p : Pattern) (guard : d10343 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10342 p = 1 := by simpa only [d10343, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27119 p hg
    simpa only [d10343, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10343, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d10343, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27121 (p : Pattern) (guard : d10345 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10343 p = 1 := by simpa only [d10345, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27120 p hg
    simpa only [d10345, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10345, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d10345, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27122 (p : Pattern) (guard : d17225 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17225, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d17225, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10345 p = 1 := by simpa only [d17225, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27121 p hg
    simpa only [d17225, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27123 (p : Pattern) (guard : d17226 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17225 p = 1 := by simpa only [d17226, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27122 p hg
    simpa only [d17226, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17226, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d17226, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27124 (p : Pattern) (guard : d17227 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2147 p = 1 := by simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27118 p hg
    simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17226 p = 1 := by simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27123 p hg
    simpa only [d17227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27125 (p : Pattern) (guard : d10349 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2009 p = 1 := by simpa only [d10349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27110 p hg
    simpa only [d10349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27126 (p : Pattern) (guard : d10350 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10349 p = 1 := by simpa only [d10350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27125 p hg
    simpa only [d10350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27127 (p : Pattern) (guard : d10351 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10350 p = 1 := by simpa only [d10351, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27126 p hg
    simpa only [d10351, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10351, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d10351, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27128 (p : Pattern) (guard : d10352 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10351 p = 1 := by simpa only [d10352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27127 p hg
    simpa only [d10352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25510 p hg
    simpa only [d10352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27129 (p : Pattern) (guard : d10353 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10352 p = 1 := by simpa only [d10353, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27128 p hg
    simpa only [d10353, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10353, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d10353, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27130 (p : Pattern) (guard : d10355 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10353 p = 1 := by simpa only [d10355, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27129 p hg
    simpa only [d10355, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10355, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d10355, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27131 (p : Pattern) (guard : d13675 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13675, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d13675, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10355 p = 1 := by simpa only [d13675, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27130 p hg
    simpa only [d13675, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27132 (p : Pattern) (guard : d13676 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13675 p = 1 := by simpa only [d13676, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27131 p hg
    simpa only [d13676, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13676, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d13676, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27133 (p : Pattern) (guard : d17228 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13676 p = 1 := by simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27132 p hg
    simpa only [d17228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27134 (p : Pattern) (guard : d17229 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17227 p = 1 := by simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27124 p hg
    simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17228 p = 1 := by simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27133 p hg
    simpa only [d17229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27135 (p : Pattern) (guard : d2013 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27100 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27136 (p : Pattern) (guard : d2014 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27101 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27135 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27137 (p : Pattern) (guard : d2015 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1999 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27102 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27136 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27138 (p : Pattern) (guard : d2016 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d2016, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25575 p hg
    simpa only [d2016, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2016, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25498 p hg
    simpa only [d2016, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27139 (p : Pattern) (guard : d2017 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27100 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2016 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27138 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27140 (p : Pattern) (guard : d2018 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2017 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27139 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27141 (p : Pattern) (guard : d2019 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27105 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2018 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27140 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27142 (p : Pattern) (guard : d2020 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2015 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27137 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2019 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27141 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27143 (p : Pattern) (guard : d2021 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d2016 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27138 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27144 (p : Pattern) (guard : d2022 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2021 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27143 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27145 (p : Pattern) (guard : d2023 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26711 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2022 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27144 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27146 (p : Pattern) (guard : d2024 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2023 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27145 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27147 (p : Pattern) (guard : d2025 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2020 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27142 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2024 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27146 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27148 (p : Pattern) (guard : d2026 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2009 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27110 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2025 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27147 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27149 (p : Pattern) (guard : d2027 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27135 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27150 (p : Pattern) (guard : d2028 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27149 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27151 (p : Pattern) (guard : d2029 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27150 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27152 (p : Pattern) (guard : d2030 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27151 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27153 (p : Pattern) (guard : d2031 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27152 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27154 (p : Pattern) (guard : d2032 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2026 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27148 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27153 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27155 (p : Pattern) (guard : d2033 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2032 p = 1 := by simpa only [d2033, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27154 p hg
    simpa only [d2033, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2033, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d2033, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27156 (p : Pattern) (guard : d2034 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2012 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27113 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2033 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27155 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27157 (p : Pattern) (guard : d2035 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2034 p = 1 := by simpa only [d2035, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27156 p hg
    simpa only [d2035, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2035, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d2035, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27158 (p : Pattern) (guard : d2036 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2035 p = 1 := by simpa only [d2036, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27157 p hg
    simpa only [d2036, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2036, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d2036, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27159 (p : Pattern) (guard : d2037 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2037, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d2037, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2036 p = 1 := by simpa only [d2037, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27158 p hg
    simpa only [d2037, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27160 (p : Pattern) (guard : d2038 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2037 p = 1 := by simpa only [d2038, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27159 p hg
    simpa only [d2038, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2038, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d2038, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27161 (p : Pattern) (guard : d10363 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2033 p = 1 := by simpa only [d10363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27155 p hg
    simpa only [d10363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25510 p hg
    simpa only [d10363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27162 (p : Pattern) (guard : d10364 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10363 p = 1 := by simpa only [d10364, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27161 p hg
    simpa only [d10364, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10364, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d10364, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27163 (p : Pattern) (guard : d10366 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10364 p = 1 := by simpa only [d10366, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27162 p hg
    simpa only [d10366, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10366, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d10366, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27164 (p : Pattern) (guard : d17153 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17153, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d17153, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10366 p = 1 := by simpa only [d17153, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27163 p hg
    simpa only [d17153, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27165 (p : Pattern) (guard : d17154 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17153 p = 1 := by simpa only [d17154, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27164 p hg
    simpa only [d17154, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17154, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d17154, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27166 (p : Pattern) (guard : d17155 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2038 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27160 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17154 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27165 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27167 (p : Pattern) (guard : d5715 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27147 p hg
    simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d5715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27168 (p : Pattern) (guard : d5716 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5715 p = 1 := by simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27167 p hg
    simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d5716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27169 (p : Pattern) (guard : d5717 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5716 p = 1 := by simpa only [d5717, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27168 p hg
    simpa only [d5717, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5717, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d5717, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27170 (p : Pattern) (guard : d2046 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2027 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27149 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27171 (p : Pattern) (guard : d5238 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2046 p = 1 := by simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27170 p hg
    simpa only [d5238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27172 (p : Pattern) (guard : d5239 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5238 p = 1 := by simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27171 p hg
    simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d5239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27173 (p : Pattern) (guard : d2047 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2046 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27170 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27174 (p : Pattern) (guard : d2048 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2047 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27173 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27175 (p : Pattern) (guard : d5243 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d5239 p = 1 := by simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27172 p hg
    simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27174 p hg
    simpa only [d5243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27176 (p : Pattern) (guard : d2061 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2048 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27174 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27177 (p : Pattern) (guard : d5244 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5243 p = 1 := by simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27175 p hg
    simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27176 p hg
    simpa only [d5244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27178 (p : Pattern) (guard : d5245 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5244 p = 1 := by simpa only [d5245, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27177 p hg
    simpa only [d5245, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5245, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d5245, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27179 (p : Pattern) (guard : d10370 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5717 p = 1 := by simpa only [d10370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27169 p hg
    simpa only [d10370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5245 p = 1 := by simpa only [d10370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27178 p hg
    simpa only [d10370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27180 (p : Pattern) (guard : d10371 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10370 p = 1 := by simpa only [d10371, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27179 p hg
    simpa only [d10371, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10371, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d10371, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27181 (p : Pattern) (guard : d10373 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10371 p = 1 := by simpa only [d10373, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27180 p hg
    simpa only [d10373, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10373, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d10373, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27182 (p : Pattern) (guard : d15548 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15548, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d15548, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10373 p = 1 := by simpa only [d15548, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27181 p hg
    simpa only [d15548, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27183 (p : Pattern) (guard : d15549 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15548 p = 1 := by simpa only [d15549, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27182 p hg
    simpa only [d15549, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15549, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d15549, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27184 (p : Pattern) (guard : d17156 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13676 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27132 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15549 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27183 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27185 (p : Pattern) (guard : d17157 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17155 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27166 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17156 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27184 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27186 (p : Pattern) (guard : d17230 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17229 p = 1 := by simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27134 p hg
    simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17157 p = 1 := by simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27185 p hg
    simpa only [d17230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27187 (p : Pattern) (guard : d19520 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d17230 p = 1 := by simpa only [d19520, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27186 p hg
    simpa only [d19520, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19520, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d19520, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27188 (p : Pattern) (guard : d19521 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19521, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d19521, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19520 p = 1 := by simpa only [d19521, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27187 p hg
    simpa only [d19521, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27189 (p : Pattern) (guard : d15550 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15549 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27183 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27190 (p : Pattern) (guard : d17233 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17156 p = 1 := by simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27184 p hg
    simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15550 p = 1 := by simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27189 p hg
    simpa only [d17233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27191 (p : Pattern) (guard : d17234 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17157 p = 1 := by simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27185 p hg
    simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17233 p = 1 := by simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27190 p hg
    simpa only [d17234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27192 (p : Pattern) (guard : d19522 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d17234 p = 1 := by simpa only [d19522, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27191 p hg
    simpa only [d19522, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19522, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d19522, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27193 (p : Pattern) (guard : d19523 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19523, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d19523, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19522 p = 1 := by simpa only [d19523, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27192 p hg
    simpa only [d19523, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27194 (p : Pattern) (guard : d19524 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19521 p = 1 := by simpa only [d19524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27188 p hg
    simpa only [d19524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19523 p = 1 := by simpa only [d19524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27193 p hg
    simpa only [d19524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27195 (p : Pattern) (guard : d2039 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27136 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27149 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27196 (p : Pattern) (guard : d2040 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2018 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27140 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27197 (p : Pattern) (guard : d2041 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2039 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27195 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27196 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27198 (p : Pattern) (guard : d2042 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2022 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27144 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27199 (p : Pattern) (guard : d2043 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2042 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27198 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27200 (p : Pattern) (guard : d2044 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2041 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27197 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27199 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27201 (p : Pattern) (guard : d2045 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27147 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2044 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27200 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27202 (p : Pattern) (guard : d2049 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27152 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27174 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27203 (p : Pattern) (guard : d2050 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2045 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27201 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27202 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27204 (p : Pattern) (guard : d2051 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2050 p = 1 := by simpa only [d2051, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27203 p hg
    simpa only [d2051, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2051, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d2051, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27205 (p : Pattern) (guard : d2052 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2033 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27155 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2051 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27204 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27206 (p : Pattern) (guard : d2053 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2052 p = 1 := by simpa only [d2053, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27205 p hg
    simpa only [d2053, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2053, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d2053, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27207 (p : Pattern) (guard : d2054 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2053 p = 1 := by simpa only [d2054, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27206 p hg
    simpa only [d2054, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2054, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d2054, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27208 (p : Pattern) (guard : d2055 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2055, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d2055, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2055, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27207 p hg
    simpa only [d2055, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27209 (p : Pattern) (guard : d2056 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27208 p hg
    simpa only [d2056, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d2056, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27210 (p : Pattern) (guard : d10390 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2051 p = 1 := by simpa only [d10390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27204 p hg
    simpa only [d10390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5245 p = 1 := by simpa only [d10390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27178 p hg
    simpa only [d10390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27211 (p : Pattern) (guard : d10391 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10390 p = 1 := by simpa only [d10391, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27210 p hg
    simpa only [d10391, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10391, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d10391, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27212 (p : Pattern) (guard : d10393 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10391 p = 1 := by simpa only [d10393, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27211 p hg
    simpa only [d10393, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10393, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d10393, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27213 (p : Pattern) (guard : d17158 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17158, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d17158, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10393 p = 1 := by simpa only [d17158, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27212 p hg
    simpa only [d17158, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27214 (p : Pattern) (guard : d17159 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17158 p = 1 := by simpa only [d17159, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27213 p hg
    simpa only [d17159, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17159, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d17159, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27215 (p : Pattern) (guard : d17160 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2056 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27209 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17159 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27214 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27216 (p : Pattern) (guard : d17161 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17160 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27215 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15550 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27189 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27217 (p : Pattern) (guard : d17162 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17157 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27185 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17161 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27216 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27218 (p : Pattern) (guard : d19525 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d17162 p = 1 := by simpa only [d19525, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27217 p hg
    simpa only [d19525, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19525, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d19525, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27219 (p : Pattern) (guard : d19526 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19526, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d19526, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19525 p = 1 := by simpa only [d19526, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27218 p hg
    simpa only [d19526, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27220 (p : Pattern) (guard : d5240 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27147 p hg
    simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5239 p = 1 := by simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27172 p hg
    simpa only [d5240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27221 (p : Pattern) (guard : d5241 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5240 p = 1 := by simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27220 p hg
    simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27202 p hg
    simpa only [d5241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27222 (p : Pattern) (guard : d5242 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5241 p = 1 := by simpa only [d5242, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27221 p hg
    simpa only [d5242, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5242, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d5242, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27223 (p : Pattern) (guard : d5246 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5242 p = 1 := by simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27222 p hg
    simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5245 p = 1 := by simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27178 p hg
    simpa only [d5246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27224 (p : Pattern) (guard : d5247 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5246 p = 1 := by simpa only [d5247, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27223 p hg
    simpa only [d5247, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5247, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d5247, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27225 (p : Pattern) (guard : d5248 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5247 p = 1 := by simpa only [d5248, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27224 p hg
    simpa only [d5248, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5248, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d5248, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27226 (p : Pattern) (guard : d5249 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5249, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d5249, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5248 p = 1 := by simpa only [d5249, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27225 p hg
    simpa only [d5249, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27227 (p : Pattern) (guard : d5250 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5249 p = 1 := by simpa only [d5250, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27226 p hg
    simpa only [d5250, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5250, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d5250, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27228 (p : Pattern) (guard : d5251 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5250 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27227 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27229 (p : Pattern) (guard : d2058 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27196 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27230 (p : Pattern) (guard : d2059 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2058 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27229 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27199 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27231 (p : Pattern) (guard : d2076 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27230 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27232 (p : Pattern) (guard : d10405 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2040 p = 1 := by simpa only [d10405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27196 p hg
    simpa only [d10405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27233 (p : Pattern) (guard : d10406 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2042 p = 1 := by simpa only [d10406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27198 p hg
    simpa only [d10406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27234 (p : Pattern) (guard : d10407 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10405 p = 1 := by simpa only [d10407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27232 p hg
    simpa only [d10407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10406 p = 1 := by simpa only [d10407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27233 p hg
    simpa only [d10407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27235 (p : Pattern) (guard : d10408 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d10407 p = 1 := by simpa only [d10408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27234 p hg
    simpa only [d10408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d10408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27236 (p : Pattern) (guard : d10409 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2076 p = 1 := by simpa only [d10409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27231 p hg
    simpa only [d10409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10408 p = 1 := by simpa only [d10409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27235 p hg
    simpa only [d10409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27237 (p : Pattern) (guard : d10410 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10409 p = 1 := by simpa only [d10410, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27236 p hg
    simpa only [d10410, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10410, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25508 p hg
    simpa only [d10410, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27238 (p : Pattern) (guard : d10411 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10410 p = 1 := by simpa only [d10411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27237 p hg
    simpa only [d10411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25510 p hg
    simpa only [d10411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27239 (p : Pattern) (guard : d10412 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10411 p = 1 := by simpa only [d10412, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27238 p hg
    simpa only [d10412, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10412, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d10412, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27240 (p : Pattern) (guard : d10414 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10412 p = 1 := by simpa only [d10414, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27239 p hg
    simpa only [d10414, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10414, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d10414, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27241 (p : Pattern) (guard : d15555 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15555, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d15555, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10414 p = 1 := by simpa only [d15555, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27240 p hg
    simpa only [d15555, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27242 (p : Pattern) (guard : d15556 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15555 p = 1 := by simpa only [d15556, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27241 p hg
    simpa only [d15556, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15556, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d15556, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27243 (p : Pattern) (guard : d15557 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15556 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27242 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27244 (p : Pattern) (guard : d15558 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5251 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27228 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27243 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27245 (p : Pattern) (guard : d17165 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27216 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15558 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27244 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27246 (p : Pattern) (guard : d19527 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d17165 p = 1 := by simpa only [d19527, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27245 p hg
    simpa only [d19527, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19527, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d19527, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27247 (p : Pattern) (guard : d19528 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19528, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d19528, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19527 p = 1 := by simpa only [d19528, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27246 p hg
    simpa only [d19528, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27248 (p : Pattern) (guard : d19529 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19526 p = 1 := by simpa only [d19529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27219 p hg
    simpa only [d19529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19528 p = 1 := by simpa only [d19529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27247 p hg
    simpa only [d19529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare27249 (p : Pattern) (guard : d19530 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d19524 p = 1 := by simpa only [d19530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27194 p hg
    simpa only [d19530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19529 p = 1 := by simpa only [d19530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27248 p hg
    simpa only [d19530, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
