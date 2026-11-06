import NetHack.Soko22Hazard87.Compare036
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare9250 (p : Pattern) (guard : d1556 p = 1) : d47736 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1555 p = 1 := by simpa only [d1556, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9249 p hg
    simpa only [d1556, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1556, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1556, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9251 (p : Pattern) (guard : d1557 p = 1) : d47737 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1557, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8000 p hg
    simpa only [d1557, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1556 p = 1 := by simpa only [d1557, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9250 p hg
    simpa only [d1557, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9252 (p : Pattern) (guard : d1558 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9251 p hg
    simpa only [d1558, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8021 p hg
    simpa only [d1558, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9253 (p : Pattern) (guard : d1559 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1541 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9235 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9254 (p : Pattern) (guard : d1560 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9242 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9253 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9255 (p : Pattern) (guard : d1561 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1560 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9254 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8851 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9256 (p : Pattern) (guard : d1562 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9239 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1561 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9255 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9257 (p : Pattern) (guard : d1563 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1547 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9241 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9258 (p : Pattern) (guard : d1564 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1563 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9257 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9259 (p : Pattern) (guard : d1565 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1564 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9258 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9260 (p : Pattern) (guard : d1566 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9244 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9259 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9261 (p : Pattern) (guard : d1567 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1562 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9256 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9260 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9262 (p : Pattern) (guard : d1568 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1567 p = 1 := by simpa only [d1568, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9261 p hg
    simpa only [d1568, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1568, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8012 p hg
    simpa only [d1568, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9263 (p : Pattern) (guard : d1569 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9247 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1568 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9262 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9264 (p : Pattern) (guard : d1570 p = 1) : d47735 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1569 p = 1 := by simpa only [d1570, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9263 p hg
    simpa only [d1570, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1570, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d1570, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9265 (p : Pattern) (guard : d1571 p = 1) : d47736 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1570 p = 1 := by simpa only [d1571, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9264 p hg
    simpa only [d1571, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1571, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1571, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9266 (p : Pattern) (guard : d1572 p = 1) : d47737 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1572, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8000 p hg
    simpa only [d1572, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1572, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9265 p hg
    simpa only [d1572, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9267 (p : Pattern) (guard : d1573 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9266 p hg
    simpa only [d1573, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8021 p hg
    simpa only [d1573, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9268 (p : Pattern) (guard : d1574 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1558 p = 1 := by simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9252 p hg
    simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1573 p = 1 := by simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9267 p hg
    simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9269 (p : Pattern) (guard : d1575 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9253 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9270 (p : Pattern) (guard : d1576 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1575 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9269 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8851 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9271 (p : Pattern) (guard : d1577 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9270 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9259 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9272 (p : Pattern) (guard : d1578 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1565 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9259 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9273 (p : Pattern) (guard : d1579 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1577 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9271 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9272 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9274 (p : Pattern) (guard : d1580 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1579 p = 1 := by simpa only [d1580, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9273 p hg
    simpa only [d1580, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1580, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8012 p hg
    simpa only [d1580, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9275 (p : Pattern) (guard : d1581 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9262 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1580 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9274 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9276 (p : Pattern) (guard : d1582 p = 1) : d47735 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9275 p hg
    simpa only [d1582, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d1582, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9277 (p : Pattern) (guard : d1583 p = 1) : d47736 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1582 p = 1 := by simpa only [d1583, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9276 p hg
    simpa only [d1583, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1583, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1583, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9278 (p : Pattern) (guard : d1584 p = 1) : d47737 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1584, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8000 p hg
    simpa only [d1584, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1584, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9277 p hg
    simpa only [d1584, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9279 (p : Pattern) (guard : d1585 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9278 p hg
    simpa only [d1585, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8021 p hg
    simpa only [d1585, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9280 (p : Pattern) (guard : d1586 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1573 p = 1 := by simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9267 p hg
    simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1585 p = 1 := by simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9279 p hg
    simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9281 (p : Pattern) (guard : d1587 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1574 p = 1 := by simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9268 p hg
    simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1586 p = 1 := by simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9280 p hg
    simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9282 (p : Pattern) (guard : d1588 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1585 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9279 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8023 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9283 (p : Pattern) (guard : d1589 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1586 p = 1 := by simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9280 p hg
    simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1588 p = 1 := by simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9282 p hg
    simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9284 (p : Pattern) (guard : d1590 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1587 p = 1 := by simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9281 p hg
    simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1589 p = 1 := by simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9283 p hg
    simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9285 (p : Pattern) (guard : d1591 p = 1) : d47756 p ≤ (-2 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1591, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7999 p hg
    simpa only [d1591, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1590 p = 1 := by simpa only [d1591, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9284 p hg
    simpa only [d1591, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9286 (p : Pattern) (guard : d1592 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1592, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7998 p hg
    simpa only [d1592, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1591 p = 1 := by simpa only [d1592, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9285 p hg
    simpa only [d1592, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9287 (p : Pattern) (guard : d1593 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9270 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9288 (p : Pattern) (guard : d1594 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1593 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9287 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9289 (p : Pattern) (guard : d1595 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1594 p = 1 := by simpa only [d1595, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9288 p hg
    simpa only [d1595, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1595, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8012 p hg
    simpa only [d1595, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9290 (p : Pattern) (guard : d1596 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1595 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9289 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8014 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9291 (p : Pattern) (guard : d1597 p = 1) : d47735 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1596 p = 1 := by simpa only [d1597, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9290 p hg
    simpa only [d1597, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1597, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d1597, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9292 (p : Pattern) (guard : d1598 p = 1) : d47736 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1597 p = 1 := by simpa only [d1598, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9291 p hg
    simpa only [d1598, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1598, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1598, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9293 (p : Pattern) (guard : d1599 p = 1) : d47737 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1599, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8000 p hg
    simpa only [d1599, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1598 p = 1 := by simpa only [d1599, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9292 p hg
    simpa only [d1599, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9294 (p : Pattern) (guard : d1600 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1599 p = 1 := by simpa only [d1600, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9293 p hg
    simpa only [d1600, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1600, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8021 p hg
    simpa only [d1600, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9295 (p : Pattern) (guard : d1601 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1600 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9294 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8023 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9296 (p : Pattern) (guard : d1602 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9282 p hg
    simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1601 p = 1 := by simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9295 p hg
    simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9297 (p : Pattern) (guard : d1603 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1589 p = 1 := by simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9283 p hg
    simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1602 p = 1 := by simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9296 p hg
    simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9298 (p : Pattern) (guard : d1604 p = 1) : d47756 p ≤ (-2 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1604, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7999 p hg
    simpa only [d1604, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1603 p = 1 := by simpa only [d1604, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9297 p hg
    simpa only [d1604, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9299 (p : Pattern) (guard : d1605 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1605, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7998 p hg
    simpa only [d1605, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1604 p = 1 := by simpa only [d1605, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9298 p hg
    simpa only [d1605, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9300 (p : Pattern) (guard : d1606 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1592 p = 1 := by simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9286 p hg
    simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1605 p = 1 := by simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9299 p hg
    simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9301 (p : Pattern) (guard : d1607 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1605 p = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9299 p hg
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9302 (p : Pattern) (guard : d1608 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1606 p = 1 := by simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9300 p hg
    simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1607 p = 1 := by simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9301 p hg
    simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9303 (p : Pattern) (guard : d1609 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1608 p = 1 := by simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9302 p hg
    simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9304 (p : Pattern) (guard : d1610 p = 1) : d47765 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1609 p = 1 := by simpa only [d1610, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9303 p hg
    simpa only [d1610, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1610, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8033 p hg
    simpa only [d1610, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9305 (p : Pattern) (guard : d1611 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1611, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7997 p hg
    simpa only [d1611, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1610 p = 1 := by simpa only [d1611, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9304 p hg
    simpa only [d1611, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9306 (p : Pattern) (guard : d1612 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1607 p = 1 := by simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9301 p hg
    simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9307 (p : Pattern) (guard : d1613 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1612 p = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9306 p hg
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9308 (p : Pattern) (guard : d1614 p = 1) : d47765 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1613 p = 1 := by simpa only [d1614, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9307 p hg
    simpa only [d1614, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1614, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8033 p hg
    simpa only [d1614, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9309 (p : Pattern) (guard : d1615 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1615, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7997 p hg
    simpa only [d1615, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1614 p = 1 := by simpa only [d1615, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9308 p hg
    simpa only [d1615, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9310 (p : Pattern) (guard : d1616 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1611 p = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9305 p hg
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1615 p = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9309 p hg
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9311 (p : Pattern) (guard : d1617 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1616 p = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9310 p hg
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9312 (p : Pattern) (guard : d1618 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1617 p = 1 := by simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9311 p hg
    simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9313 (p : Pattern) (guard : d1632 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1618 p = 1 := by simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9312 p hg
    simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9314 (p : Pattern) (guard : d1620 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1615 p = 1 := by simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9309 p hg
    simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9315 (p : Pattern) (guard : d1621 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1620 p = 1 := by simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9314 p hg
    simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9316 (p : Pattern) (guard : d1622 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1621 p = 1 := by simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9315 p hg
    simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9317 (p : Pattern) (guard : d1633 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1622 p = 1 := by simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9316 p hg
    simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9318 (p : Pattern) (guard : d1634 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1632 p = 1 := by simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9313 p hg
    simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1633 p = 1 := by simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9317 p hg
    simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9319 (p : Pattern) (guard : d1635 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1634 p = 1 := by simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9318 p hg
    simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9320 (p : Pattern) (guard : d1636 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1635 p = 1 := by simpa only [d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9319 p hg
    simpa only [d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9321 (p : Pattern) (guard : d1637 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1636 p = 1 := by simpa only [d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9320 p hg
    simpa only [d1637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9322 (p : Pattern) (guard : d1638 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1637 p = 1 := by simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9321 p hg
    simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9323 (p : Pattern) (guard : d53764 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53764, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53764, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1638 p = 1 := by simpa only [d53764, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9322 p hg
    simpa only [d53764, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9324 (p : Pattern) (guard : d53765 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53764 p = 1 := by simpa only [d53765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9323 p hg
    simpa only [d53765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9325 (p : Pattern) (guard : d53766 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 69 with
  | false =>
    have hg : d53765 p = 1 := by simpa only [d53766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9324 p hg
    simpa only [d53766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9326 (p : Pattern) (guard : d53767 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 51 with
  | false =>
    have hg : d53766 p = 1 := by simpa only [d53767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9325 p hg
    simpa only [d53767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9327 (p : Pattern) (guard : d53768 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 50 with
  | false =>
    have hg : d53767 p = 1 := by simpa only [d53768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9326 p hg
    simpa only [d53768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9328 (p : Pattern) (guard : d53769 p = 1) : d47768 p ≤ (-2 : Int) + d98793 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53763 p = 1 := by simpa only [d53769, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9205 p hg
    simpa only [d53769, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53768 p = 1 := by simpa only [d53769, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9327 p hg
    simpa only [d53769, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9329 (p : Pattern) (guard : d1199 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8910 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9330 (p : Pattern) (guard : d1200 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1199 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9329 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9331 (p : Pattern) (guard : d1201 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1200 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9330 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9332 (p : Pattern) (guard : d308 p = 1) : d2 p ≤ (-2 : Int) + d12 p := by
  have ha := bounds2 p
  have hb := bounds12 p
  omega
theorem compare9333 (p : Pattern) (guard : d1519 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9332 p hg
    simpa only [d1519, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8057 p hg
    simpa only [d1519, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9334 (p : Pattern) (guard : d1520 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8396 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1519 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9333 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9335 (p : Pattern) (guard : d1521 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8605 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1520 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9334 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9336 (p : Pattern) (guard : d1522 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8910 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1521 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9335 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9337 (p : Pattern) (guard : d1523 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1523, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8914 p hg
    simpa only [d1523, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d1523, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8395 p hg
    simpa only [d1523, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9338 (p : Pattern) (guard : d1524 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9337 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1084 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8915 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9339 (p : Pattern) (guard : d1525 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9338 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9340 (p : Pattern) (guard : d1526 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1525 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9339 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9341 (p : Pattern) (guard : d1527 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1522 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9336 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1526 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9340 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9342 (p : Pattern) (guard : d1528 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8918 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9343 (p : Pattern) (guard : d1529 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1527 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9341 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1528 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9342 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9344 (p : Pattern) (guard : d1530 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9331 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1529 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9343 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9345 (p : Pattern) (guard : d1203 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8923 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9346 (p : Pattern) (guard : d1204 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1203 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9345 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9347 (p : Pattern) (guard : d1205 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1204 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9346 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9348 (p : Pattern) (guard : d1531 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9333 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9349 (p : Pattern) (guard : d1532 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9334 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1531 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9348 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9350 (p : Pattern) (guard : d1533 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8923 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9349 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9351 (p : Pattern) (guard : d1534 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1533 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9350 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9352 (p : Pattern) (guard : d1535 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1534 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9351 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9353 (p : Pattern) (guard : d1536 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9347 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1535 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9352 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9354 (p : Pattern) (guard : d1537 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1530 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9344 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1536 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9353 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9355 (p : Pattern) (guard : d1538 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1537 p = 1 := by simpa only [d1538, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9354 p hg
    simpa only [d1538, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1538, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d1538, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9356 (p : Pattern) (guard : d1539 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1521 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9335 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9349 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9357 (p : Pattern) (guard : d1540 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9333 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8058 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9358 (p : Pattern) (guard : d1541 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9357 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9359 (p : Pattern) (guard : d1542 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1525 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9339 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9358 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9360 (p : Pattern) (guard : d1543 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1539 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9356 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1542 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9359 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9361 (p : Pattern) (guard : d1544 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8930 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9362 (p : Pattern) (guard : d1545 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1543 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9360 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1544 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9361 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9363 (p : Pattern) (guard : d1546 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9343 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1545 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9362 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9364 (p : Pattern) (guard : d1547 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9348 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9365 (p : Pattern) (guard : d1548 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9349 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9364 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9366 (p : Pattern) (guard : d1549 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9365 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9367 (p : Pattern) (guard : d1550 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1549 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9366 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9368 (p : Pattern) (guard : d1551 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1535 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9352 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1550 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9367 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9369 (p : Pattern) (guard : d1552 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1546 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9363 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1551 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9368 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9370 (p : Pattern) (guard : d1553 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9369 p hg
    simpa only [d1553, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d1553, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9371 (p : Pattern) (guard : d1554 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1538 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9355 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9370 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9372 (p : Pattern) (guard : d1857 p = 1) : d47652 p ≤ (-2 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1857, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8055 p hg
    simpa only [d1857, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1554 p = 1 := by simpa only [d1857, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9371 p hg
    simpa only [d1857, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9373 (p : Pattern) (guard : d1555 p = 1) : d47797 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1554 p = 1 := by simpa only [d1555, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9118 p hg
    simpa only [d1555, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1555, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d1555, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9374 (p : Pattern) (guard : d1858 p = 1) : d47798 p ≤ (-2 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1857 p = 1 := by simpa only [d1858, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9372 p hg
    simpa only [d1858, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1555 p = 1 := by simpa only [d1858, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9373 p hg
    simpa only [d1858, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9375 (p : Pattern) (guard : d1199 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8940 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9376 (p : Pattern) (guard : d1200 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1199 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9375 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9377 (p : Pattern) (guard : d1201 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1200 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9376 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9378 (p : Pattern) (guard : d308 p = 1) : d6 p ≤ (-2 : Int) + d12 p := by
  have ha := bounds6 p
  have hb := bounds12 p
  omega
theorem compare9379 (p : Pattern) (guard : d1519 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9378 p hg
    simpa only [d1519, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8075 p hg
    simpa only [d1519, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9380 (p : Pattern) (guard : d1520 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8412 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1519 p = 1 := by simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9379 p hg
    simpa only [d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9381 (p : Pattern) (guard : d1521 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8623 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1520 p = 1 := by simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9380 p hg
    simpa only [d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9382 (p : Pattern) (guard : d1522 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8940 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1521 p = 1 := by simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9381 p hg
    simpa only [d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9383 (p : Pattern) (guard : d1523 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1523, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8944 p hg
    simpa only [d1523, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d1523, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8411 p hg
    simpa only [d1523, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9384 (p : Pattern) (guard : d1524 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9383 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1084 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8945 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9385 (p : Pattern) (guard : d1525 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9384 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9386 (p : Pattern) (guard : d1526 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1525 p = 1 := by simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9385 p hg
    simpa only [d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9387 (p : Pattern) (guard : d1527 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1522 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9382 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1526 p = 1 := by simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9386 p hg
    simpa only [d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9388 (p : Pattern) (guard : d1528 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8948 p hg
    simpa only [d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9389 (p : Pattern) (guard : d1529 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1527 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9387 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1528 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9388 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9390 (p : Pattern) (guard : d1530 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9377 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1529 p = 1 := by simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9389 p hg
    simpa only [d1530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9391 (p : Pattern) (guard : d1203 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8953 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9392 (p : Pattern) (guard : d1204 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1203 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9391 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9393 (p : Pattern) (guard : d1205 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1204 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9392 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9394 (p : Pattern) (guard : d1531 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9379 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9395 (p : Pattern) (guard : d1532 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9380 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1531 p = 1 := by simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9394 p hg
    simpa only [d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9396 (p : Pattern) (guard : d1533 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8953 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9395 p hg
    simpa only [d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9397 (p : Pattern) (guard : d1534 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1533 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9396 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9398 (p : Pattern) (guard : d1535 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1534 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9397 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9399 (p : Pattern) (guard : d1536 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9393 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1535 p = 1 := by simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9398 p hg
    simpa only [d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9400 (p : Pattern) (guard : d1537 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1530 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9390 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1536 p = 1 := by simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9399 p hg
    simpa only [d1537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9401 (p : Pattern) (guard : d1538 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1537 p = 1 := by simpa only [d1538, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9400 p hg
    simpa only [d1538, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1538, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d1538, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9402 (p : Pattern) (guard : d1539 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1521 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9381 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1532 p = 1 := by simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9395 p hg
    simpa only [d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9403 (p : Pattern) (guard : d1540 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9379 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15 p = 1 := by simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8076 p hg
    simpa only [d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9404 (p : Pattern) (guard : d1541 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9403 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9405 (p : Pattern) (guard : d1542 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1525 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9385 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9404 p hg
    simpa only [d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9406 (p : Pattern) (guard : d1543 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1539 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9402 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1542 p = 1 := by simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9405 p hg
    simpa only [d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9407 (p : Pattern) (guard : d1544 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8960 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9408 (p : Pattern) (guard : d1545 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1543 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9406 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1544 p = 1 := by simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9407 p hg
    simpa only [d1545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9409 (p : Pattern) (guard : d1546 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1529 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9389 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1545 p = 1 := by simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9408 p hg
    simpa only [d1546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9410 (p : Pattern) (guard : d1547 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9394 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9411 (p : Pattern) (guard : d1548 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9395 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9410 p hg
    simpa only [d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9412 (p : Pattern) (guard : d1549 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9411 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9413 (p : Pattern) (guard : d1550 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1549 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9412 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9414 (p : Pattern) (guard : d1551 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1535 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9398 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1550 p = 1 := by simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9413 p hg
    simpa only [d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9415 (p : Pattern) (guard : d1552 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1546 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9409 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1551 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9414 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9416 (p : Pattern) (guard : d1553 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9415 p hg
    simpa only [d1553, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d1553, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9417 (p : Pattern) (guard : d1554 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1538 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9401 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9416 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9418 (p : Pattern) (guard : d1555 p = 1) : d47682 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1554 p = 1 := by simpa only [d1555, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9417 p hg
    simpa only [d1555, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1555, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1555, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9419 (p : Pattern) (guard : d1556 p = 1) : d47683 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1555 p = 1 := by simpa only [d1556, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9418 p hg
    simpa only [d1556, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1556, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1556, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9420 (p : Pattern) (guard : d1859 p = 1) : d47799 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1858 p = 1 := by simpa only [d1859, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9374 p hg
    simpa only [d1859, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1556 p = 1 := by simpa only [d1859, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9419 p hg
    simpa only [d1859, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9421 (p : Pattern) (guard : d1860 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1859 p = 1 := by simpa only [d1860, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9420 p hg
    simpa only [d1860, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1860, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d1860, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9422 (p : Pattern) (guard : d1559 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1541 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9358 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9423 (p : Pattern) (guard : d1560 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9365 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9422 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9424 (p : Pattern) (guard : d1561 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1560 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9423 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8991 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9425 (p : Pattern) (guard : d1562 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9362 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1561 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9424 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9426 (p : Pattern) (guard : d1563 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1547 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9364 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9427 (p : Pattern) (guard : d1564 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1563 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9426 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9428 (p : Pattern) (guard : d1565 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1564 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9427 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9429 (p : Pattern) (guard : d1566 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9367 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9428 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9430 (p : Pattern) (guard : d1567 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1562 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9425 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9429 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9431 (p : Pattern) (guard : d1568 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1567 p = 1 := by simpa only [d1568, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9430 p hg
    simpa only [d1568, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1568, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d1568, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9432 (p : Pattern) (guard : d1569 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9370 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1568 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9431 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9433 (p : Pattern) (guard : d1862 p = 1) : d47652 p ≤ (-2 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1862, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8055 p hg
    simpa only [d1862, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1569 p = 1 := by simpa only [d1862, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9432 p hg
    simpa only [d1862, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9434 (p : Pattern) (guard : d1570 p = 1) : d47797 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1569 p = 1 := by simpa only [d1570, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9133 p hg
    simpa only [d1570, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1570, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d1570, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9435 (p : Pattern) (guard : d1863 p = 1) : d47798 p ≤ (-2 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1862 p = 1 := by simpa only [d1863, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9433 p hg
    simpa only [d1863, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1570 p = 1 := by simpa only [d1863, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9434 p hg
    simpa only [d1863, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9436 (p : Pattern) (guard : d1559 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1541 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9404 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9437 (p : Pattern) (guard : d1560 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1548 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9411 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9436 p hg
    simpa only [d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9438 (p : Pattern) (guard : d1561 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1560 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9437 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9000 p hg
    simpa only [d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9439 (p : Pattern) (guard : d1562 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9408 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1561 p = 1 := by simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9438 p hg
    simpa only [d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9440 (p : Pattern) (guard : d1563 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1547 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9410 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9441 (p : Pattern) (guard : d1564 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1563 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9440 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9442 (p : Pattern) (guard : d1565 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1564 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9441 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9443 (p : Pattern) (guard : d1566 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9413 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9442 p hg
    simpa only [d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9444 (p : Pattern) (guard : d1567 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1562 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9439 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9443 p hg
    simpa only [d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9445 (p : Pattern) (guard : d1568 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1567 p = 1 := by simpa only [d1568, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9444 p hg
    simpa only [d1568, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1568, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d1568, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9446 (p : Pattern) (guard : d1569 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9416 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1568 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9445 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9447 (p : Pattern) (guard : d1570 p = 1) : d47682 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1569 p = 1 := by simpa only [d1570, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9446 p hg
    simpa only [d1570, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1570, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1570, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9448 (p : Pattern) (guard : d1571 p = 1) : d47683 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1570 p = 1 := by simpa only [d1571, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9447 p hg
    simpa only [d1571, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1571, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1571, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9449 (p : Pattern) (guard : d1864 p = 1) : d47799 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1863 p = 1 := by simpa only [d1864, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9435 p hg
    simpa only [d1864, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1864, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9448 p hg
    simpa only [d1864, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9450 (p : Pattern) (guard : d1865 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1864 p = 1 := by simpa only [d1865, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9449 p hg
    simpa only [d1865, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1865, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d1865, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9451 (p : Pattern) (guard : d1866 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1860 p = 1 := by simpa only [d1866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9421 p hg
    simpa only [d1866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1865 p = 1 := by simpa only [d1866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9450 p hg
    simpa only [d1866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9452 (p : Pattern) (guard : d1575 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9422 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9453 (p : Pattern) (guard : d1576 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1575 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9452 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8991 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9454 (p : Pattern) (guard : d1577 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9453 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9428 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9455 (p : Pattern) (guard : d1578 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1565 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9428 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9456 (p : Pattern) (guard : d1579 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1577 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9454 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9455 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9457 (p : Pattern) (guard : d1580 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1579 p = 1 := by simpa only [d1580, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9456 p hg
    simpa only [d1580, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1580, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d1580, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9458 (p : Pattern) (guard : d1581 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9431 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1580 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9457 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9459 (p : Pattern) (guard : d1868 p = 1) : d47652 p ≤ (-2 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1868, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8055 p hg
    simpa only [d1868, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1581 p = 1 := by simpa only [d1868, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9458 p hg
    simpa only [d1868, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9460 (p : Pattern) (guard : d1582 p = 1) : d47797 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9145 p hg
    simpa only [d1582, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d1582, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9461 (p : Pattern) (guard : d1869 p = 1) : d47798 p ≤ (-2 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1868 p = 1 := by simpa only [d1869, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9459 p hg
    simpa only [d1869, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1582 p = 1 := by simpa only [d1869, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9460 p hg
    simpa only [d1869, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9462 (p : Pattern) (guard : d1575 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9436 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9463 (p : Pattern) (guard : d1576 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1575 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9462 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9000 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9464 (p : Pattern) (guard : d1577 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9463 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9442 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9465 (p : Pattern) (guard : d1578 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1565 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9442 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9466 (p : Pattern) (guard : d1579 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1577 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9464 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9465 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9467 (p : Pattern) (guard : d1580 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1579 p = 1 := by simpa only [d1580, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9466 p hg
    simpa only [d1580, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1580, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d1580, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9468 (p : Pattern) (guard : d1581 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9445 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1580 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9467 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9469 (p : Pattern) (guard : d1582 p = 1) : d47682 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9468 p hg
    simpa only [d1582, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1582, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9470 (p : Pattern) (guard : d1583 p = 1) : d47683 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1582 p = 1 := by simpa only [d1583, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9469 p hg
    simpa only [d1583, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1583, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1583, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9471 (p : Pattern) (guard : d1870 p = 1) : d47799 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1869 p = 1 := by simpa only [d1870, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9461 p hg
    simpa only [d1870, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1870, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9470 p hg
    simpa only [d1870, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9472 (p : Pattern) (guard : d1871 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1870 p = 1 := by simpa only [d1871, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9471 p hg
    simpa only [d1871, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1871, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d1871, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9473 (p : Pattern) (guard : d1872 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1865 p = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9450 p hg
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1871 p = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9472 p hg
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9474 (p : Pattern) (guard : d1873 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1866 p = 1 := by simpa only [d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9451 p hg
    simpa only [d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1872 p = 1 := by simpa only [d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9473 p hg
    simpa only [d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9475 (p : Pattern) (guard : d1877 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1871 p = 1 := by simpa only [d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9472 p hg
    simpa only [d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8094 p hg
    simpa only [d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9476 (p : Pattern) (guard : d1878 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1872 p = 1 := by simpa only [d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9473 p hg
    simpa only [d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1877 p = 1 := by simpa only [d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9475 p hg
    simpa only [d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9477 (p : Pattern) (guard : d1879 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1873 p = 1 := by simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9474 p hg
    simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1878 p = 1 := by simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9476 p hg
    simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9478 (p : Pattern) (guard : d1880 p = 1) : d47804 p ≤ (-2 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1880, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8054 p hg
    simpa only [d1880, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1879 p = 1 := by simpa only [d1880, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9477 p hg
    simpa only [d1880, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9479 (p : Pattern) (guard : d1881 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1881, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8053 p hg
    simpa only [d1881, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1880 p = 1 := by simpa only [d1881, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9478 p hg
    simpa only [d1881, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9480 (p : Pattern) (guard : d1593 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9453 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9481 (p : Pattern) (guard : d1594 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1593 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9480 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9482 (p : Pattern) (guard : d1595 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1594 p = 1 := by simpa only [d1595, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9481 p hg
    simpa only [d1595, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1595, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d1595, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9483 (p : Pattern) (guard : d1596 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1595 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9482 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8069 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9484 (p : Pattern) (guard : d1883 p = 1) : d47652 p ≤ (-2 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1883, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8055 p hg
    simpa only [d1883, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1596 p = 1 := by simpa only [d1883, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9483 p hg
    simpa only [d1883, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9485 (p : Pattern) (guard : d1597 p = 1) : d47797 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1596 p = 1 := by simpa only [d1597, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9160 p hg
    simpa only [d1597, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1597, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d1597, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9486 (p : Pattern) (guard : d1884 p = 1) : d47798 p ≤ (-2 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1883 p = 1 := by simpa only [d1884, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9484 p hg
    simpa only [d1884, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1597 p = 1 := by simpa only [d1884, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9485 p hg
    simpa only [d1884, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9487 (p : Pattern) (guard : d1593 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9463 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9488 (p : Pattern) (guard : d1594 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1593 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9487 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9489 (p : Pattern) (guard : d1595 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1594 p = 1 := by simpa only [d1595, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9488 p hg
    simpa only [d1595, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1595, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d1595, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9490 (p : Pattern) (guard : d1596 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1595 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9489 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8087 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9491 (p : Pattern) (guard : d1597 p = 1) : d47682 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1596 p = 1 := by simpa only [d1597, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9490 p hg
    simpa only [d1597, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1597, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1597, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9492 (p : Pattern) (guard : d1598 p = 1) : d47683 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1597 p = 1 := by simpa only [d1598, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9491 p hg
    simpa only [d1598, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1598, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d1598, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9493 (p : Pattern) (guard : d1885 p = 1) : d47799 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1884 p = 1 := by simpa only [d1885, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9486 p hg
    simpa only [d1885, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1598 p = 1 := by simpa only [d1885, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9492 p hg
    simpa only [d1885, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9494 (p : Pattern) (guard : d1886 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1885 p = 1 := by simpa only [d1886, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9493 p hg
    simpa only [d1886, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1886, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d1886, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9495 (p : Pattern) (guard : d1887 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1886 p = 1 := by simpa only [d1887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9494 p hg
    simpa only [d1887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8094 p hg
    simpa only [d1887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9496 (p : Pattern) (guard : d1888 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1877 p = 1 := by simpa only [d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9475 p hg
    simpa only [d1888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1887 p = 1 := by simpa only [d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9495 p hg
    simpa only [d1888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9497 (p : Pattern) (guard : d1889 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1878 p = 1 := by simpa only [d1889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9476 p hg
    simpa only [d1889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1888 p = 1 := by simpa only [d1889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9496 p hg
    simpa only [d1889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9498 (p : Pattern) (guard : d1890 p = 1) : d47804 p ≤ (-2 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1890, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8054 p hg
    simpa only [d1890, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1889 p = 1 := by simpa only [d1890, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9497 p hg
    simpa only [d1890, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9499 (p : Pattern) (guard : d1891 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1891, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8053 p hg
    simpa only [d1891, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1890 p = 1 := by simpa only [d1891, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9498 p hg
    simpa only [d1891, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
