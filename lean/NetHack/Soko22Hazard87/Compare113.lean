import NetHack.Soko22Hazard87.Compare112
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare28250 (p : Pattern) (guard : d10135 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10134 p = 1 := by simpa only [d10135, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28249 p hg
    simpa only [d10135, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10135, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d10135, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28251 (p : Pattern) (guard : d10137 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10135 p = 1 := by simpa only [d10137, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28250 p hg
    simpa only [d10137, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10137, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d10137, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28252 (p : Pattern) (guard : d15163 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15163, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d15163, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10137 p = 1 := by simpa only [d15163, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28251 p hg
    simpa only [d15163, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28253 (p : Pattern) (guard : d15164 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15163 p = 1 := by simpa only [d15164, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28252 p hg
    simpa only [d15164, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15164, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d15164, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28254 (p : Pattern) (guard : d15165 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15164 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28253 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28255 (p : Pattern) (guard : d15166 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5138 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28240 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28254 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28256 (p : Pattern) (guard : d16799 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28226 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15166 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28255 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28257 (p : Pattern) (guard : d16800 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16800, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d16800, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16799 p = 1 := by simpa only [d16800, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28256 p hg
    simpa only [d16800, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28258 (p : Pattern) (guard : d16801 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16801, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d16801, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16800 p = 1 := by simpa only [d16801, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28257 p hg
    simpa only [d16801, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28259 (p : Pattern) (guard : d16802 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16798 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28229 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16801 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28258 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28260 (p : Pattern) (guard : d1577 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28242 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28195 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28261 (p : Pattern) (guard : d1579 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1577 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28260 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28197 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28262 (p : Pattern) (guard : d1580 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1579 p = 1 := by simpa only [d1580, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28261 p hg
    simpa only [d1580, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1580, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d1580, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28263 (p : Pattern) (guard : d1581 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28213 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1580 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28262 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28264 (p : Pattern) (guard : d1582 p = 1) : d48407 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28263 p hg
    simpa only [d1582, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27423 p hg
    simpa only [d1582, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28265 (p : Pattern) (guard : d1583 p = 1) : d48571 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1582 p = 1 := by simpa only [d1583, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28264 p hg
    simpa only [d1583, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1583, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27425 p hg
    simpa only [d1583, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28266 (p : Pattern) (guard : d1584 p = 1) : d48698 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1584, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27407 p hg
    simpa only [d1584, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1584, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28265 p hg
    simpa only [d1584, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28267 (p : Pattern) (guard : d1585 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28266 p hg
    simpa only [d1585, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27428 p hg
    simpa only [d1585, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28268 (p : Pattern) (guard : d1588 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1585 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28267 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28269 (p : Pattern) (guard : d15171 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28268 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28254 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28270 (p : Pattern) (guard : d16803 p = 1) : d48701 p ≤ (-2 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28226 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15171 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28269 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28271 (p : Pattern) (guard : d16804 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16804, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d16804, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16803 p = 1 := by simpa only [d16804, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28270 p hg
    simpa only [d16804, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28272 (p : Pattern) (guard : d16805 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16805, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d16805, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16804 p = 1 := by simpa only [d16805, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28271 p hg
    simpa only [d16805, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28273 (p : Pattern) (guard : d16806 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16805 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28272 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28274 (p : Pattern) (guard : d16807 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28259 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16806 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28273 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28275 (p : Pattern) (guard : d1199 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27953 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28276 (p : Pattern) (guard : d1200 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1199 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28275 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28277 (p : Pattern) (guard : d1201 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1200 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28276 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28278 (p : Pattern) (guard : d1520 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27604 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1519 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27986 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28279 (p : Pattern) (guard : d1521 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27729 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1520 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28278 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28280 (p : Pattern) (guard : d1522 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27953 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1521 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28279 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28281 (p : Pattern) (guard : d1523 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1523, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27957 p hg
    simpa only [d1523, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d1523, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27603 p hg
    simpa only [d1523, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28282 (p : Pattern) (guard : d1524 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28281 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1084 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27958 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28283 (p : Pattern) (guard : d1525 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28282 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28284 (p : Pattern) (guard : d1526 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1525 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28283 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28285 (p : Pattern) (guard : d1527 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1522 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28280 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1526 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28284 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28286 (p : Pattern) (guard : d1528 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27961 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28287 (p : Pattern) (guard : d1529 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1527 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28285 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1528 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28286 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28288 (p : Pattern) (guard : d1530 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28277 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1529 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28287 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28289 (p : Pattern) (guard : d1203 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27966 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28290 (p : Pattern) (guard : d1204 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1203 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28289 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28291 (p : Pattern) (guard : d1205 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1204 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28290 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28292 (p : Pattern) (guard : d1532 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28278 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1531 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27987 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28293 (p : Pattern) (guard : d1533 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27966 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28292 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28294 (p : Pattern) (guard : d1534 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1533 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28293 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28295 (p : Pattern) (guard : d1535 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1534 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28294 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28296 (p : Pattern) (guard : d1536 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28291 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1535 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28295 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28297 (p : Pattern) (guard : d1537 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1530 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28288 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1536 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28296 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28298 (p : Pattern) (guard : d1538 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1537 p = 1 := by simpa only [d1538, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28297 p hg
    simpa only [d1538, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1538, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d1538, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28299 (p : Pattern) (guard : d1539 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1521 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28279 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28292 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28300 (p : Pattern) (guard : d1540 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27986 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27442 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28301 (p : Pattern) (guard : d1541 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28300 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28302 (p : Pattern) (guard : d1542 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1525 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28283 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28301 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28303 (p : Pattern) (guard : d1543 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1539 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28299 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1542 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28302 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28304 (p : Pattern) (guard : d1544 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27973 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28305 (p : Pattern) (guard : d1545 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1543 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28303 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1544 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28304 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28306 (p : Pattern) (guard : d1546 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28287 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1545 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28305 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28307 (p : Pattern) (guard : d1547 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27987 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28308 (p : Pattern) (guard : d1548 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28292 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28307 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28309 (p : Pattern) (guard : d1549 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28308 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28310 (p : Pattern) (guard : d1550 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1549 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28309 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28311 (p : Pattern) (guard : d1551 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1535 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28295 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1550 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28310 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28312 (p : Pattern) (guard : d1552 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1546 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28306 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1551 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28311 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28313 (p : Pattern) (guard : d1553 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28312 p hg
    simpa only [d1553, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d1553, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28314 (p : Pattern) (guard : d1554 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1538 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28298 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28313 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28315 (p : Pattern) (guard : d1555 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1554 p = 1 := by simpa only [d1555, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28314 p hg
    simpa only [d1555, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1555, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d1555, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28316 (p : Pattern) (guard : d1556 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1555 p = 1 := by simpa only [d1556, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28315 p hg
    simpa only [d1556, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1556, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d1556, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28317 (p : Pattern) (guard : d1557 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1557, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d1557, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1556 p = 1 := by simpa only [d1557, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28316 p hg
    simpa only [d1557, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28318 (p : Pattern) (guard : d1558 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28317 p hg
    simpa only [d1558, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d1558, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28319 (p : Pattern) (guard : d2005 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28281 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28320 (p : Pattern) (guard : d2006 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28319 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28321 (p : Pattern) (guard : d10054 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28320 p hg
    simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28322 (p : Pattern) (guard : d10055 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10054 p = 1 := by simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28321 p hg
    simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28323 (p : Pattern) (guard : d10056 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10055 p = 1 := by simpa only [d10056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28322 p hg
    simpa only [d10056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d10056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28324 (p : Pattern) (guard : d5122 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5121 p = 1 := by simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27984 p hg
    simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28307 p hg
    simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28325 (p : Pattern) (guard : d10057 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5122 p = 1 := by simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28324 p hg
    simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28326 (p : Pattern) (guard : d10058 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10057 p = 1 := by simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28325 p hg
    simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28327 (p : Pattern) (guard : d10059 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d10056 p = 1 := by simpa only [d10059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28323 p hg
    simpa only [d10059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10058 p = 1 := by simpa only [d10059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28326 p hg
    simpa only [d10059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28328 (p : Pattern) (guard : d10060 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10059 p = 1 := by simpa only [d10060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28327 p hg
    simpa only [d10060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d10060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28329 (p : Pattern) (guard : d10061 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10060 p = 1 := by simpa only [d10061, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28328 p hg
    simpa only [d10061, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10061, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d10061, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28330 (p : Pattern) (guard : d10073 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d10073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28313 p hg
    simpa only [d10073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10061 p = 1 := by simpa only [d10073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28329 p hg
    simpa only [d10073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28331 (p : Pattern) (guard : d10074 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10073 p = 1 := by simpa only [d10074, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28330 p hg
    simpa only [d10074, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10074, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d10074, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28332 (p : Pattern) (guard : d10076 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10074 p = 1 := by simpa only [d10076, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28331 p hg
    simpa only [d10076, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10076, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d10076, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28333 (p : Pattern) (guard : d16787 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16787, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d16787, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10076 p = 1 := by simpa only [d16787, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28332 p hg
    simpa only [d16787, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28334 (p : Pattern) (guard : d16788 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16787 p = 1 := by simpa only [d16788, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28333 p hg
    simpa only [d16788, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16788, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d16788, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28335 (p : Pattern) (guard : d16789 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1558 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28318 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16788 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28334 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28336 (p : Pattern) (guard : d10051 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d10051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28287 p hg
    simpa only [d10051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d10051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28337 (p : Pattern) (guard : d10052 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10051 p = 1 := by simpa only [d10052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28336 p hg
    simpa only [d10052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d10052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28338 (p : Pattern) (guard : d10053 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10052 p = 1 := by simpa only [d10053, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28337 p hg
    simpa only [d10053, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10053, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d10053, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28339 (p : Pattern) (guard : d10062 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10053 p = 1 := by simpa only [d10062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28338 p hg
    simpa only [d10062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10061 p = 1 := by simpa only [d10062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28329 p hg
    simpa only [d10062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28340 (p : Pattern) (guard : d10063 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10062 p = 1 := by simpa only [d10063, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28339 p hg
    simpa only [d10063, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10063, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d10063, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28341 (p : Pattern) (guard : d10065 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10063 p = 1 := by simpa only [d10065, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28340 p hg
    simpa only [d10065, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10065, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d10065, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28342 (p : Pattern) (guard : d15151 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15151, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d15151, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10065 p = 1 := by simpa only [d15151, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28341 p hg
    simpa only [d15151, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28343 (p : Pattern) (guard : d15152 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15151 p = 1 := by simpa only [d15152, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28342 p hg
    simpa only [d15152, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15152, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d15152, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28344 (p : Pattern) (guard : d10080 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28305 p hg
    simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10058 p = 1 := by simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28326 p hg
    simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28345 (p : Pattern) (guard : d10081 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28310 p hg
    simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28346 (p : Pattern) (guard : d10082 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10080 p = 1 := by simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28344 p hg
    simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10081 p = 1 := by simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28345 p hg
    simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28347 (p : Pattern) (guard : d10083 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10082 p = 1 := by simpa only [d10083, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28346 p hg
    simpa only [d10083, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10083, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d10083, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28348 (p : Pattern) (guard : d1563 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1547 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28307 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28349 (p : Pattern) (guard : d5128 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1563 p = 1 := by simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28348 p hg
    simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28350 (p : Pattern) (guard : d5129 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5128 p = 1 := by simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28349 p hg
    simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28351 (p : Pattern) (guard : d1564 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1563 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28348 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28352 (p : Pattern) (guard : d1565 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1564 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28351 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28353 (p : Pattern) (guard : d5130 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d5129 p = 1 := by simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28350 p hg
    simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28352 p hg
    simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28354 (p : Pattern) (guard : d1578 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1565 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28352 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28355 (p : Pattern) (guard : d5131 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5130 p = 1 := by simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28353 p hg
    simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28354 p hg
    simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28356 (p : Pattern) (guard : d5132 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5131 p = 1 := by simpa only [d5132, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28355 p hg
    simpa only [d5132, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5132, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d5132, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28357 (p : Pattern) (guard : d10084 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10083 p = 1 := by simpa only [d10084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28347 p hg
    simpa only [d10084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5132 p = 1 := by simpa only [d10084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28356 p hg
    simpa only [d10084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28358 (p : Pattern) (guard : d10085 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10084 p = 1 := by simpa only [d10085, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28357 p hg
    simpa only [d10085, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10085, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d10085, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28359 (p : Pattern) (guard : d10087 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10085 p = 1 := by simpa only [d10087, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28358 p hg
    simpa only [d10087, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10087, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d10087, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28360 (p : Pattern) (guard : d15156 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15156, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d15156, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10087 p = 1 := by simpa only [d15156, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28359 p hg
    simpa only [d15156, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28361 (p : Pattern) (guard : d15157 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15156 p = 1 := by simpa only [d15157, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28360 p hg
    simpa only [d15157, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15157, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d15157, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28362 (p : Pattern) (guard : d16790 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15152 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28343 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15157 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28361 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28363 (p : Pattern) (guard : d16791 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16789 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28335 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16790 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28362 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28364 (p : Pattern) (guard : d1559 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1541 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28301 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28365 (p : Pattern) (guard : d1560 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28308 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28364 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28366 (p : Pattern) (guard : d1561 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1560 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28365 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28016 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28367 (p : Pattern) (guard : d1562 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28305 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1561 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28366 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28368 (p : Pattern) (guard : d1566 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28310 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28352 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28369 (p : Pattern) (guard : d1567 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1562 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28367 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28368 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28370 (p : Pattern) (guard : d1568 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1567 p = 1 := by simpa only [d1568, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28369 p hg
    simpa only [d1568, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1568, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d1568, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28371 (p : Pattern) (guard : d1569 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28313 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1568 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28370 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28372 (p : Pattern) (guard : d1570 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1569 p = 1 := by simpa only [d1570, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28371 p hg
    simpa only [d1570, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1570, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d1570, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28373 (p : Pattern) (guard : d1571 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1570 p = 1 := by simpa only [d1571, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28372 p hg
    simpa only [d1571, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1571, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d1571, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28374 (p : Pattern) (guard : d1572 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1572, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d1572, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1572, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28373 p hg
    simpa only [d1572, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28375 (p : Pattern) (guard : d1573 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28374 p hg
    simpa only [d1573, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d1573, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28376 (p : Pattern) (guard : d10114 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d10114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28370 p hg
    simpa only [d10114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5132 p = 1 := by simpa only [d10114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28356 p hg
    simpa only [d10114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28377 (p : Pattern) (guard : d10115 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10114 p = 1 := by simpa only [d10115, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28376 p hg
    simpa only [d10115, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10115, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d10115, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28378 (p : Pattern) (guard : d10117 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10115 p = 1 := by simpa only [d10117, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28377 p hg
    simpa only [d10117, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10117, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d10117, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28379 (p : Pattern) (guard : d16792 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16792, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d16792, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10117 p = 1 := by simpa only [d16792, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28378 p hg
    simpa only [d16792, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28380 (p : Pattern) (guard : d16793 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16792 p = 1 := by simpa only [d16793, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28379 p hg
    simpa only [d16793, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16793, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d16793, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28381 (p : Pattern) (guard : d16794 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1573 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28375 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16793 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28380 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28382 (p : Pattern) (guard : d15158 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15157 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28361 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28383 (p : Pattern) (guard : d16795 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16794 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28381 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15158 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28382 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28384 (p : Pattern) (guard : d16796 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16791 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28363 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16795 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28383 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28385 (p : Pattern) (guard : d19293 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16796 p = 1 := by simpa only [d19293, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28384 p hg
    simpa only [d19293, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19293, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d19293, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28386 (p : Pattern) (guard : d19294 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19294, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d19294, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19293 p = 1 := by simpa only [d19294, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28385 p hg
    simpa only [d19294, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28387 (p : Pattern) (guard : d5123 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5122 p = 1 := by simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28324 p hg
    simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1563 p = 1 := by simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28348 p hg
    simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28388 (p : Pattern) (guard : d5124 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5123 p = 1 := by simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28387 p hg
    simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28389 (p : Pattern) (guard : d5125 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28305 p hg
    simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5124 p = 1 := by simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28388 p hg
    simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28390 (p : Pattern) (guard : d5126 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5125 p = 1 := by simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28389 p hg
    simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28368 p hg
    simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28391 (p : Pattern) (guard : d5127 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5126 p = 1 := by simpa only [d5127, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28390 p hg
    simpa only [d5127, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5127, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d5127, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28392 (p : Pattern) (guard : d5133 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5127 p = 1 := by simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28391 p hg
    simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5132 p = 1 := by simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28356 p hg
    simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28393 (p : Pattern) (guard : d5134 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5133 p = 1 := by simpa only [d5134, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28392 p hg
    simpa only [d5134, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5134, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d5134, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28394 (p : Pattern) (guard : d5135 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5134 p = 1 := by simpa only [d5135, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28393 p hg
    simpa only [d5135, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5135, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d5135, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28395 (p : Pattern) (guard : d5136 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5136, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d5136, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5135 p = 1 := by simpa only [d5136, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28394 p hg
    simpa only [d5136, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28396 (p : Pattern) (guard : d5137 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5136 p = 1 := by simpa only [d5137, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28395 p hg
    simpa only [d5137, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5137, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d5137, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28397 (p : Pattern) (guard : d5138 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5137 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28396 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28398 (p : Pattern) (guard : d1575 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28364 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28399 (p : Pattern) (guard : d1576 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1575 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28398 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28016 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28400 (p : Pattern) (guard : d1593 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28399 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28401 (p : Pattern) (guard : d10129 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1559 p = 1 := by simpa only [d10129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28364 p hg
    simpa only [d10129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d10129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28402 (p : Pattern) (guard : d10130 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10129 p = 1 := by simpa only [d10130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28401 p hg
    simpa only [d10130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19 p = 1 := by simpa only [d10130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27447 p hg
    simpa only [d10130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28403 (p : Pattern) (guard : d10131 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d10130 p = 1 := by simpa only [d10131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28402 p hg
    simpa only [d10131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27443 p hg
    simpa only [d10131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28404 (p : Pattern) (guard : d10132 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1593 p = 1 := by simpa only [d10132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28400 p hg
    simpa only [d10132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10131 p = 1 := by simpa only [d10132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28403 p hg
    simpa only [d10132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28405 (p : Pattern) (guard : d10133 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10132 p = 1 := by simpa only [d10133, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28404 p hg
    simpa only [d10133, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10133, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d10133, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28406 (p : Pattern) (guard : d10134 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10133 p = 1 := by simpa only [d10134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28405 p hg
    simpa only [d10134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27453 p hg
    simpa only [d10134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28407 (p : Pattern) (guard : d10135 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10134 p = 1 := by simpa only [d10135, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28406 p hg
    simpa only [d10135, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10135, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d10135, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28408 (p : Pattern) (guard : d10137 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10135 p = 1 := by simpa only [d10137, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28407 p hg
    simpa only [d10137, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10137, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d10137, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28409 (p : Pattern) (guard : d15163 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15163, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d15163, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10137 p = 1 := by simpa only [d15163, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28408 p hg
    simpa only [d15163, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28410 (p : Pattern) (guard : d15164 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15163 p = 1 := by simpa only [d15164, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28409 p hg
    simpa only [d15164, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15164, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d15164, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28411 (p : Pattern) (guard : d15165 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15164 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28410 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28412 (p : Pattern) (guard : d15166 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5138 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28397 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28411 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28413 (p : Pattern) (guard : d16799 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28383 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15166 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28412 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28414 (p : Pattern) (guard : d19295 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16799 p = 1 := by simpa only [d19295, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28413 p hg
    simpa only [d19295, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19295, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d19295, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28415 (p : Pattern) (guard : d19296 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19296, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d19296, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19295 p = 1 := by simpa only [d19296, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28414 p hg
    simpa only [d19296, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28416 (p : Pattern) (guard : d19297 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19294 p = 1 := by simpa only [d19297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28386 p hg
    simpa only [d19297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19296 p = 1 := by simpa only [d19297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28415 p hg
    simpa only [d19297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28417 (p : Pattern) (guard : d1577 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28399 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28352 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28418 (p : Pattern) (guard : d1579 p = 1) : d47613 p ≤ (-2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1577 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28417 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28354 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28419 (p : Pattern) (guard : d1580 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1579 p = 1 := by simpa only [d1580, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28418 p hg
    simpa only [d1580, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1580, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27451 p hg
    simpa only [d1580, d47615, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28420 (p : Pattern) (guard : d1581 p = 1) : d47615 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28370 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1580 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28419 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28421 (p : Pattern) (guard : d1582 p = 1) : d47653 p ≤ (-2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28420 p hg
    simpa only [d1582, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27455 p hg
    simpa only [d1582, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28422 (p : Pattern) (guard : d1583 p = 1) : d48565 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1582 p = 1 := by simpa only [d1583, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28421 p hg
    simpa only [d1583, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1583, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27457 p hg
    simpa only [d1583, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28423 (p : Pattern) (guard : d1584 p = 1) : d48601 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1584, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27439 p hg
    simpa only [d1584, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1584, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28422 p hg
    simpa only [d1584, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28424 (p : Pattern) (guard : d1585 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28423 p hg
    simpa only [d1585, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27460 p hg
    simpa only [d1585, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28425 (p : Pattern) (guard : d1588 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1585 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28424 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27406 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28426 (p : Pattern) (guard : d15171 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28425 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28411 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28427 (p : Pattern) (guard : d16803 p = 1) : d48602 p ≤ (-2 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28383 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15171 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28426 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28428 (p : Pattern) (guard : d19323 p = 1) : d48702 p ≤ (-2 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16803 p = 1 := by simpa only [d19323, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28427 p hg
    simpa only [d19323, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19323, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27430 p hg
    simpa only [d19323, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28429 (p : Pattern) (guard : d19324 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d19324, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27405 p hg
    simpa only [d19324, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19323 p = 1 := by simpa only [d19324, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28428 p hg
    simpa only [d19324, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28430 (p : Pattern) (guard : d19325 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d19324 p = 1 := by simpa only [d19325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28429 p hg
    simpa only [d19325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d19325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28431 (p : Pattern) (guard : d132484 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d19297 p = 1 := by simpa only [d132484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28416 p hg
    simpa only [d132484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19325 p = 1 := by simpa only [d132484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28430 p hg
    simpa only [d132484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28432 (p : Pattern) (guard : d188384 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16807 p = 1 := by simpa only [d188384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28274 p hg
    simpa only [d188384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d132484 p = 1 := by simpa only [d188384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28431 p hg
    simpa only [d188384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28433 (p : Pattern) (guard : d188385 p = 1) : d48705 p ≤ (-2 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188384 p = 1 := by simpa only [d188385, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28432 p hg
    simpa only [d188385, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188385, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27470 p hg
    simpa only [d188385, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28434 (p : Pattern) (guard : d188386 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188386, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27404 p hg
    simpa only [d188386, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188385 p = 1 := by simpa only [d188386, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28433 p hg
    simpa only [d188386, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28435 (p : Pattern) (guard : d16811 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16806 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28273 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28436 (p : Pattern) (guard : d19326 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d19325 p = 1 := by simpa only [d19326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28430 p hg
    simpa only [d19326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27436 p hg
    simpa only [d19326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28437 (p : Pattern) (guard : d188138 p = 1) : d48703 p ≤ (-2 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16811 p = 1 := by simpa only [d188138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28435 p hg
    simpa only [d188138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19326 p = 1 := by simpa only [d188138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28436 p hg
    simpa only [d188138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28438 (p : Pattern) (guard : d188139 p = 1) : d48705 p ≤ (-2 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188138 p = 1 := by simpa only [d188139, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28437 p hg
    simpa only [d188139, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188139, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27470 p hg
    simpa only [d188139, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28439 (p : Pattern) (guard : d188140 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188140, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27404 p hg
    simpa only [d188140, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188139 p = 1 := by simpa only [d188140, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28438 p hg
    simpa only [d188140, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28440 (p : Pattern) (guard : d188387 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188386 p = 1 := by simpa only [d188387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28434 p hg
    simpa only [d188387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188140 p = 1 := by simpa only [d188387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28439 p hg
    simpa only [d188387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28441 (p : Pattern) (guard : d188388 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188387 p = 1 := by simpa only [d188388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28440 p hg
    simpa only [d188388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28442 (p : Pattern) (guard : d188389 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188388 p = 1 := by simpa only [d188389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28441 p hg
    simpa only [d188389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28443 (p : Pattern) (guard : d188390 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188389 p = 1 := by simpa only [d188390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28442 p hg
    simpa only [d188390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28444 (p : Pattern) (guard : d188161 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188140 p = 1 := by simpa only [d188161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28439 p hg
    simpa only [d188161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28445 (p : Pattern) (guard : d188162 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188161 p = 1 := by simpa only [d188162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28444 p hg
    simpa only [d188162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28446 (p : Pattern) (guard : d188163 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188162 p = 1 := by simpa only [d188163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28445 p hg
    simpa only [d188163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28447 (p : Pattern) (guard : d188164 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188163 p = 1 := by simpa only [d188164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28446 p hg
    simpa only [d188164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28448 (p : Pattern) (guard : d188391 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d188390 p = 1 := by simpa only [d188391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28443 p hg
    simpa only [d188391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188164 p = 1 := by simpa only [d188391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28447 p hg
    simpa only [d188391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28449 (p : Pattern) (guard : d188392 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188391 p = 1 := by simpa only [d188392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28448 p hg
    simpa only [d188392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28450 (p : Pattern) (guard : d188393 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d188392 p = 1 := by simpa only [d188393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28449 p hg
    simpa only [d188393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28451 (p : Pattern) (guard : d188394 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188393 p = 1 := by simpa only [d188394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28450 p hg
    simpa only [d188394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28452 (p : Pattern) (guard : d188395 p = 1) : d48706 p ≤ (-2 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27403 p hg
    simpa only [d188395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188394 p = 1 := by simpa only [d188395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28451 p hg
    simpa only [d188395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28453 (p : Pattern) (guard : d188396 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188396, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27402 p hg
    simpa only [d188396, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188395 p = 1 := by simpa only [d188396, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28452 p hg
    simpa only [d188396, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28454 (p : Pattern) (guard : d188397 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188396 p = 1 := by simpa only [d188397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28453 p hg
    simpa only [d188397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28455 (p : Pattern) (guard : d188398 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 69 with
  | false =>
    have hg : d188397 p = 1 := by simpa only [d188398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28454 p hg
    simpa only [d188398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28456 (p : Pattern) (guard : d188399 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 51 with
  | false =>
    have hg : d188398 p = 1 := by simpa only [d188399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28455 p hg
    simpa only [d188399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28457 (p : Pattern) (guard : d188400 p = 1) : d48707 p ≤ (-2 : Int) + d188508 p := by
  cases selected : p 50 with
  | false =>
    have hg : d188399 p = 1 := by simpa only [d188400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28456 p hg
    simpa only [d188400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27401 p hg
    simpa only [d188400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28458 (p : Pattern) (guard : d188401 p = 1) : d48748 p ≤ (-2 : Int) + d188517 p := by
  cases selected : p 49 with
  | false =>
    have hg : d188400 p = 1 := by simpa only [d188401, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28457 p hg
    simpa only [d188401, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188401, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27487 p hg
    simpa only [d188401, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28459 (p : Pattern) (guard : d188402 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188402, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27400 p hg
    simpa only [d188402, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188401 p = 1 := by simpa only [d188402, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28458 p hg
    simpa only [d188402, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28460 (p : Pattern) (guard : d188403 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188402 p = 1 := by simpa only [d188403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28459 p hg
    simpa only [d188403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28461 (p : Pattern) (guard : d188404 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188403 p = 1 := by simpa only [d188404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28460 p hg
    simpa only [d188404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28462 (p : Pattern) (guard : d188405 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188404 p = 1 := by simpa only [d188405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28461 p hg
    simpa only [d188405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28463 (p : Pattern) (guard : d188406 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188405 p = 1 := by simpa only [d188406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28462 p hg
    simpa only [d188406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28464 (p : Pattern) (guard : d188407 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188406 p = 1 := by simpa only [d188407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28463 p hg
    simpa only [d188407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28465 (p : Pattern) (guard : d188408 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188407 p = 1 := by simpa only [d188408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28464 p hg
    simpa only [d188408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28466 (p : Pattern) (guard : d188409 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188408 p = 1 := by simpa only [d188409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28465 p hg
    simpa only [d188409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28467 (p : Pattern) (guard : d188410 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188409 p = 1 := by simpa only [d188410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28466 p hg
    simpa only [d188410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28468 (p : Pattern) (guard : d188411 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27399 p hg
    simpa only [d188411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188410 p = 1 := by simpa only [d188411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28467 p hg
    simpa only [d188411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28469 (p : Pattern) (guard : d188412 p = 1) : d48749 p ≤ (-2 : Int) + d188518 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d188383 p = 1 := by simpa only [d188412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28117 p hg
    simpa only [d188412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188411 p = 1 := by simpa only [d188412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28468 p hg
    simpa only [d188412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28470 (p : Pattern) (guard : d1997 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27568 p hg
    simpa only [d1997, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27409 p hg
    simpa only [d1997, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28471 (p : Pattern) (guard : d1998 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28470 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28472 (p : Pattern) (guard : d1999 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28471 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28473 (p : Pattern) (guard : d2000 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28472 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28474 (p : Pattern) (guard : d2001 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1523 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28124 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28475 (p : Pattern) (guard : d2002 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2001 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28474 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28476 (p : Pattern) (guard : d2003 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2002 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28475 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28477 (p : Pattern) (guard : d2004 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28473 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2003 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28476 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28478 (p : Pattern) (guard : d2007 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28163 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28479 (p : Pattern) (guard : d2008 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2007 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28478 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28480 (p : Pattern) (guard : d2009 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2004 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28477 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2008 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28479 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28481 (p : Pattern) (guard : d2010 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2009 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28480 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28482 (p : Pattern) (guard : d2011 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2010 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28481 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28483 (p : Pattern) (guard : d2012 p = 1) : d47652 p ≤ (-2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2011 p = 1 := by simpa only [d2012, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28482 p hg
    simpa only [d2012, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2012, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27419 p hg
    simpa only [d2012, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28484 (p : Pattern) (guard : d2013 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28470 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28485 (p : Pattern) (guard : d2014 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28471 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28484 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28486 (p : Pattern) (guard : d2015 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1999 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28472 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28485 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28487 (p : Pattern) (guard : d2016 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d2016, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27495 p hg
    simpa only [d2016, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2016, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27409 p hg
    simpa only [d2016, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28488 (p : Pattern) (guard : d2017 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28470 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2016 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28487 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28489 (p : Pattern) (guard : d2018 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2017 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28488 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28490 (p : Pattern) (guard : d2019 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28475 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2018 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28489 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28491 (p : Pattern) (guard : d2020 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2015 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28486 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2019 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28490 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28492 (p : Pattern) (guard : d2021 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d2016 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28487 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28493 (p : Pattern) (guard : d2022 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2021 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28492 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28494 (p : Pattern) (guard : d2023 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28163 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2022 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28493 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28495 (p : Pattern) (guard : d2024 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2023 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28494 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28496 (p : Pattern) (guard : d2025 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2020 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28491 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2024 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28495 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28497 (p : Pattern) (guard : d2026 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2009 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28480 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2025 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28496 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28498 (p : Pattern) (guard : d2027 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28484 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare28499 (p : Pattern) (guard : d2028 p = 1) : d47630 p ≤ (-2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27411 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28498 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
