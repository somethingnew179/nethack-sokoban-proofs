/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons315
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare44240 (p : Pattern) (guard : d8112 p = 1) : d124 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43957 p hg
    simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44012 p hg
    simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44241 (p : Pattern) (guard : d8118 p = 1) : d1577 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1577, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44240 p hg
    simpa only [d8118, d1577, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1577, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35740 p hg
    simpa only [d8118, d1577, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44242 (p : Pattern) (guard : d8124 p = 1) : d1578 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1578, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44241 p hg
    simpa only [d8124, d1578, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1578, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35322 p hg
    simpa only [d8124, d1578, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44243 (p : Pattern) (guard : d8125 p = 1) : d1579 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1579, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44239 p hg
    simpa only [d8125, d1579, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1579, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44242 p hg
    simpa only [d8125, d1579, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44244 (p : Pattern) (guard : d8105 p = 1) : d336 p ≤ (0 : Int) + d336 p := by
  omega
theorem compare44245 (p : Pattern) (guard : d8106 p = 1) : d1580 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1580, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35748 p hg
    simpa only [d8106, d1580, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1580, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44244 p hg
    simpa only [d8106, d1580, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44246 (p : Pattern) (guard : d8111 p = 1) : d139 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d139, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35755 p hg
    simpa only [d8111, d139, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d139, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d139, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44247 (p : Pattern) (guard : d8112 p = 1) : d1581 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1581, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44245 p hg
    simpa only [d8112, d1581, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1581, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44246 p hg
    simpa only [d8112, d1581, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44248 (p : Pattern) (guard : d8111 p = 1) : d125 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d125, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35762 p hg
    simpa only [d8111, d125, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d125, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d125, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44249 (p : Pattern) (guard : d8117 p = 1) : d215 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d215, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44248 p hg
    simpa only [d8117, d215, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d215, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35764 p hg
    simpa only [d8117, d215, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44250 (p : Pattern) (guard : d8118 p = 1) : d1640 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1640, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44247 p hg
    simpa only [d8118, d1640, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1640, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44249 p hg
    simpa only [d8118, d1640, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44251 (p : Pattern) (guard : d8117 p = 1) : d215 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d215, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44232 p hg
    simpa only [d8117, d215, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d215, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35767 p hg
    simpa only [d8117, d215, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44252 (p : Pattern) (guard : d8123 p = 1) : d217 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d217, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44251 p hg
    simpa only [d8123, d217, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d217, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d217, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44253 (p : Pattern) (guard : d8124 p = 1) : d1641 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1641, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44250 p hg
    simpa only [d8124, d1641, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1641, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44252 p hg
    simpa only [d8124, d1641, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44254 (p : Pattern) (guard : d8111 p = 1) : d124 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d124, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35775 p hg
    simpa only [d8111, d124, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d124, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d124, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44255 (p : Pattern) (guard : d8117 p = 1) : d1584 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1584, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44254 p hg
    simpa only [d8117, d1584, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1584, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10971 p hg
    simpa only [d8117, d1584, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44256 (p : Pattern) (guard : d8123 p = 1) : d1642 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1642, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44255 p hg
    simpa only [d8123, d1642, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1642, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35778 p hg
    simpa only [d8123, d1642, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44257 (p : Pattern) (guard : d8129 p = 1) : d1643 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1643, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44256 p hg
    simpa only [d8129, d1643, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1643, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13622 p hg
    simpa only [d8129, d1643, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44258 (p : Pattern) (guard : d8130 p = 1) : d1644 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1644, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44253 p hg
    simpa only [d8130, d1644, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1644, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44257 p hg
    simpa only [d8130, d1644, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44259 (p : Pattern) (guard : d8131 p = 1) : d1645 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1645, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44243 p hg
    simpa only [d8131, d1645, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1645, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44258 p hg
    simpa only [d8131, d1645, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44260 (p : Pattern) (guard : d8112 p = 1) : d124 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43981 p hg
    simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44254 p hg
    simpa only [d8112, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44261 (p : Pattern) (guard : d8117 p = 1) : d126 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d126, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44012 p hg
    simpa only [d8117, d126, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d126, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3761 p hg
    simpa only [d8117, d126, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44262 (p : Pattern) (guard : d8118 p = 1) : d1577 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1577, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44260 p hg
    simpa only [d8118, d1577, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1577, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44261 p hg
    simpa only [d8118, d1577, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44263 (p : Pattern) (guard : d8123 p = 1) : d129 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d129, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35740 p hg
    simpa only [d8123, d129, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d129, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4322 p hg
    simpa only [d8123, d129, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44264 (p : Pattern) (guard : d8124 p = 1) : d1578 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1578, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44262 p hg
    simpa only [d8124, d1578, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1578, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44263 p hg
    simpa only [d8124, d1578, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44265 (p : Pattern) (guard : d8130 p = 1) : d1590 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1590, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44264 p hg
    simpa only [d8130, d1590, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1590, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44000 p hg
    simpa only [d8130, d1590, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44266 (p : Pattern) (guard : d8111 p = 1) : d124 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d124, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35796 p hg
    simpa only [d8111, d124, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d124, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d124, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44267 (p : Pattern) (guard : d0 p = 1) : d139 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44268 (p : Pattern) (guard : d8117 p = 1) : d1584 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1584, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44266 p hg
    simpa only [d8117, d1584, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1584, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44267 p hg
    simpa only [d8117, d1584, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44269 (p : Pattern) (guard : d8123 p = 1) : d1642 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1642, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44268 p hg
    simpa only [d8123, d1642, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1642, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35778 p hg
    simpa only [d8123, d1642, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44270 (p : Pattern) (guard : d8129 p = 1) : d1643 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1643, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44269 p hg
    simpa only [d8129, d1643, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1643, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13622 p hg
    simpa only [d8129, d1643, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44271 (p : Pattern) (guard : d8135 p = 1) : d1646 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1646, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44270 p hg
    simpa only [d8135, d1646, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1646, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11992 p hg
    simpa only [d8135, d1646, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44272 (p : Pattern) (guard : d8136 p = 1) : d1647 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1647, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44265 p hg
    simpa only [d8136, d1647, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1647, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44271 p hg
    simpa only [d8136, d1647, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44273 (p : Pattern) (guard : d8137 p = 1) : d1648 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1648, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44259 p hg
    simpa only [d8137, d1648, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1648, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44272 p hg
    simpa only [d8137, d1648, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44274 (p : Pattern) (guard : d8112 p = 1) : d124 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44231 p hg
    simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44266 p hg
    simpa only [d8112, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44275 (p : Pattern) (guard : d8117 p = 1) : d126 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d126, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44254 p hg
    simpa only [d8117, d126, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d126, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3761 p hg
    simpa only [d8117, d126, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44276 (p : Pattern) (guard : d8118 p = 1) : d1577 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1577, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44274 p hg
    simpa only [d8118, d1577, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1577, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44275 p hg
    simpa only [d8118, d1577, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44277 (p : Pattern) (guard : d8123 p = 1) : d129 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d129, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44261 p hg
    simpa only [d8123, d129, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d129, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4322 p hg
    simpa only [d8123, d129, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44278 (p : Pattern) (guard : d8124 p = 1) : d1578 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1578, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44276 p hg
    simpa only [d8124, d1578, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1578, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44277 p hg
    simpa only [d8124, d1578, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44279 (p : Pattern) (guard : d8117 p = 1) : d1053 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1053, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43937 p hg
    simpa only [d8117, d1053, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1053, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8222 p hg
    simpa only [d8117, d1053, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44280 (p : Pattern) (guard : d8123 p = 1) : d1054 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1054, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44279 p hg
    simpa only [d8123, d1054, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1054, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1054, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44281 (p : Pattern) (guard : d8129 p = 1) : d1589 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1589, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44280 p hg
    simpa only [d8129, d1589, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1589, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1589, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44282 (p : Pattern) (guard : d8130 p = 1) : d1590 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1590, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44278 p hg
    simpa only [d8130, d1590, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1590, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44281 p hg
    simpa only [d8130, d1590, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44283 (p : Pattern) (guard : d8111 p = 1) : d124 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d124, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35819 p hg
    simpa only [d8111, d124, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d124, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d124, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44284 (p : Pattern) (guard : d0 p = 1) : d139 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44285 (p : Pattern) (guard : d8117 p = 1) : d1584 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1584, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44283 p hg
    simpa only [d8117, d1584, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1584, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44284 p hg
    simpa only [d8117, d1584, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44286 (p : Pattern) (guard : d0 p = 1) : d215 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44287 (p : Pattern) (guard : d8123 p = 1) : d1642 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1642, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44285 p hg
    simpa only [d8123, d1642, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1642, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44286 p hg
    simpa only [d8123, d1642, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44288 (p : Pattern) (guard : d8129 p = 1) : d1643 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1643, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44287 p hg
    simpa only [d8129, d1643, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1643, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13622 p hg
    simpa only [d8129, d1643, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44289 (p : Pattern) (guard : d8135 p = 1) : d1646 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1646, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44288 p hg
    simpa only [d8135, d1646, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1646, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11992 p hg
    simpa only [d8135, d1646, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44290 (p : Pattern) (guard : d8136 p = 1) : d1647 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1647, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44282 p hg
    simpa only [d8136, d1647, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1647, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44289 p hg
    simpa only [d8136, d1647, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44291 (p : Pattern) (guard : d8123 p = 1) : d1595 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1595, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44237 p hg
    simpa only [d8123, d1595, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1595, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1595, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44292 (p : Pattern) (guard : d8129 p = 1) : d1596 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1596, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44291 p hg
    simpa only [d8129, d1596, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1596, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1596, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44293 (p : Pattern) (guard : d8135 p = 1) : d1597 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1597, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44292 p hg
    simpa only [d8135, d1597, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1597, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d1597, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44294 (p : Pattern) (guard : d8141 p = 1) : d1598 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d1598, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44293 p hg
    simpa only [d8141, d1598, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d1598, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8141, d1598, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44295 (p : Pattern) (guard : d8142 p = 1) : d1649 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1649, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44290 p hg
    simpa only [d8142, d1649, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1649, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44294 p hg
    simpa only [d8142, d1649, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44296 (p : Pattern) (guard : d8143 p = 1) : d1650 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d1650, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44273 p hg
    simpa only [d8143, d1650, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d1650, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44295 p hg
    simpa only [d8143, d1650, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44297 (p : Pattern) (guard : d8112 p = 1) : d1601 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1601, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44229 p hg
    simpa only [d8112, d1601, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1601, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44283 p hg
    simpa only [d8112, d1601, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44298 (p : Pattern) (guard : d0 p = 1) : d125 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44299 (p : Pattern) (guard : d8117 p = 1) : d126 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d126, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44266 p hg
    simpa only [d8117, d126, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d126, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44298 p hg
    simpa only [d8117, d126, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44300 (p : Pattern) (guard : d8118 p = 1) : d1602 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1602, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44297 p hg
    simpa only [d8118, d1602, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1602, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44299 p hg
    simpa only [d8118, d1602, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44301 (p : Pattern) (guard : d8123 p = 1) : d129 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d129, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44275 p hg
    simpa only [d8123, d129, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d129, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4322 p hg
    simpa only [d8123, d129, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44302 (p : Pattern) (guard : d8124 p = 1) : d1603 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1603, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44300 p hg
    simpa only [d8124, d1603, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1603, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44301 p hg
    simpa only [d8124, d1603, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44303 (p : Pattern) (guard : d8117 p = 1) : d139 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43958 p hg
    simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10971 p hg
    simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44304 (p : Pattern) (guard : d8123 p = 1) : d1651 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1651, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44303 p hg
    simpa only [d8123, d1651, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1651, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35778 p hg
    simpa only [d8123, d1651, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44305 (p : Pattern) (guard : d8129 p = 1) : d1652 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1652, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44304 p hg
    simpa only [d8129, d1652, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1652, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13638 p hg
    simpa only [d8129, d1652, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44306 (p : Pattern) (guard : d8130 p = 1) : d1653 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1653, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44302 p hg
    simpa only [d8130, d1653, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1653, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44305 p hg
    simpa only [d8130, d1653, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44307 (p : Pattern) (guard : d8111 p = 1) : d124 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d124, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35837 p hg
    simpa only [d8111, d124, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d124, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d124, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44308 (p : Pattern) (guard : d0 p = 1) : d139 p ≤ (0 : Int) + d360 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44309 (p : Pattern) (guard : d8117 p = 1) : d1584 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1584, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44307 p hg
    simpa only [d8117, d1584, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1584, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44308 p hg
    simpa only [d8117, d1584, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44310 (p : Pattern) (guard : d0 p = 1) : d215 p ≤ (0 : Int) + d371 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44311 (p : Pattern) (guard : d8123 p = 1) : d1642 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1642, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44309 p hg
    simpa only [d8123, d1642, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1642, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44310 p hg
    simpa only [d8123, d1642, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44312 (p : Pattern) (guard : d0 p = 1) : d217 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44313 (p : Pattern) (guard : d8129 p = 1) : d1643 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1643, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44311 p hg
    simpa only [d8129, d1643, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1643, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44312 p hg
    simpa only [d8129, d1643, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44314 (p : Pattern) (guard : d8135 p = 1) : d1656 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1656, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44313 p hg
    simpa only [d8135, d1656, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1656, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12061 p hg
    simpa only [d8135, d1656, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44315 (p : Pattern) (guard : d8136 p = 1) : d1657 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1657, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44306 p hg
    simpa only [d8136, d1657, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1657, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44314 p hg
    simpa only [d8136, d1657, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44316 (p : Pattern) (guard : d0 p = 1) : d124 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44317 (p : Pattern) (guard : d8117 p = 1) : d124 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44254 p hg
    simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44316 p hg
    simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44318 (p : Pattern) (guard : d0 p = 1) : d1658 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44319 (p : Pattern) (guard : d8123 p = 1) : d1659 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1659, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44317 p hg
    simpa only [d8123, d1659, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1659, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44318 p hg
    simpa only [d8123, d1659, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44320 (p : Pattern) (guard : d8129 p = 1) : d1660 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1660, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44319 p hg
    simpa only [d8129, d1660, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1660, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13566 p hg
    simpa only [d8129, d1660, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44321 (p : Pattern) (guard : d8135 p = 1) : d1661 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1661, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44320 p hg
    simpa only [d8135, d1661, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1661, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11992 p hg
    simpa only [d8135, d1661, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44322 (p : Pattern) (guard : d0 p = 1) : d1663 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44323 (p : Pattern) (guard : d8141 p = 1) : d1664 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d1664, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44321 p hg
    simpa only [d8141, d1664, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d1664, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44322 p hg
    simpa only [d8141, d1664, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44324 (p : Pattern) (guard : d8142 p = 1) : d1665 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1665, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44315 p hg
    simpa only [d8142, d1665, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1665, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44323 p hg
    simpa only [d8142, d1665, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44325 (p : Pattern) (guard : d0 p = 1) : d124 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44326 (p : Pattern) (guard : d8117 p = 1) : d124 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44266 p hg
    simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44325 p hg
    simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44327 (p : Pattern) (guard : d0 p = 1) : d1666 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44328 (p : Pattern) (guard : d8123 p = 1) : d1667 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1667, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44326 p hg
    simpa only [d8123, d1667, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1667, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44327 p hg
    simpa only [d8123, d1667, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44329 (p : Pattern) (guard : d8129 p = 1) : d1670 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1670, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44328 p hg
    simpa only [d8129, d1670, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1670, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13644 p hg
    simpa only [d8129, d1670, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44330 (p : Pattern) (guard : d8135 p = 1) : d1674 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1674, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44329 p hg
    simpa only [d8135, d1674, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1674, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12082 p hg
    simpa only [d8135, d1674, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44331 (p : Pattern) (guard : d0 p = 1) : d1663 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44332 (p : Pattern) (guard : d8141 p = 1) : d1675 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d1675, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44330 p hg
    simpa only [d8141, d1675, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d1675, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44331 p hg
    simpa only [d8141, d1675, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44333 (p : Pattern) (guard : d8147 p = 1) : d1676 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8141 p = 1 := by simpa only [d8147, d1676, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44332 p hg
    simpa only [d8147, d1676, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8147, d1676, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8147, d1676, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44334 (p : Pattern) (guard : d8148 p = 1) : d1677 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d1677, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44324 p hg
    simpa only [d8148, d1677, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d1677, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44333 p hg
    simpa only [d8148, d1677, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44335 (p : Pattern) (guard : d8149 p = 1) : d1678 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d1678, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44296 p hg
    simpa only [d8149, d1678, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d1678, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44334 p hg
    simpa only [d8149, d1678, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44336 (p : Pattern) (guard : d8150 p = 1) : d1679 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d1679, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44225 p hg
    simpa only [d8150, d1679, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d1679, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44335 p hg
    simpa only [d8150, d1679, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44337 (p : Pattern) (guard : d8151 p = 1) : d1680 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d1680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44138 p hg
    simpa only [d8151, d1680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d1680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44336 p hg
    simpa only [d8151, d1680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44338 (p : Pattern) (guard : d8152 p = 1) : d1681 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d1681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44022 p hg
    simpa only [d8152, d1681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d1681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44337 p hg
    simpa only [d8152, d1681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44339 (p : Pattern) (guard : d1 p = 1) : d190 p ≤ (0 : Int) + d190 p := by
  omega
theorem compare44340 (p : Pattern) (guard : d1 p = 1) : d3225 p ≤ (0 : Int) + d314 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3225, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33794 p hg
    simpa only [d3225, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3225, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44339 p hg
    simpa only [d3225, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44341 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3226, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33795 p hg
    simpa only [d3226, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3226, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3226, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44342 (p : Pattern) (guard : d1 p = 1) : d3227 p ≤ (0 : Int) + d316 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3227, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44340 p hg
    simpa only [d3227, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3227, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44341 p hg
    simpa only [d3227, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44343 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3226, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33799 p hg
    simpa only [d3226, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3226, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3226, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44344 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44345 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44343 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44344 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44346 (p : Pattern) (guard : d1 p = 1) : d3228 p ≤ (0 : Int) + d319 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3228, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44342 p hg
    simpa only [d3228, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3228, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44345 p hg
    simpa only [d3228, d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44347 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44341 p hg
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44344 p hg
    simpa only [d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44348 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44347 p hg
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44344 p hg
    simpa only [d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44349 (p : Pattern) (guard : d1 p = 1) : d3229 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3229, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44346 p hg
    simpa only [d3229, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3229, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44348 p hg
    simpa only [d3229, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44350 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44345 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44344 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44351 (p : Pattern) (guard : d8087 p = 1) : d3230 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d3230, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44350 p hg
    simpa only [d8087, d3230, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d3230, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34328 p hg
    simpa only [d8087, d3230, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44352 (p : Pattern) (guard : d8088 p = 1) : d3231 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8088, d3231, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44349 p hg
    simpa only [d8088, d3231, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8087 p = 1 := by simpa only [d8088, d3231, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44351 p hg
    simpa only [d8088, d3231, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44353 (p : Pattern) (guard : d1 p = 1) : d3232 p ≤ (0 : Int) + d326 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3232, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33810 p hg
    simpa only [d3232, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3232, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36103 p hg
    simpa only [d3232, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44354 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3226, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33811 p hg
    simpa only [d3226, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3226, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3226, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44355 (p : Pattern) (guard : d1 p = 1) : d3233 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3233, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44353 p hg
    simpa only [d3233, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3233, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44354 p hg
    simpa only [d3233, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44356 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3226, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33816 p hg
    simpa only [d3226, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3226, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3226, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44357 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44356 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44344 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44358 (p : Pattern) (guard : d1 p = 1) : d3234 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3234, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44355 p hg
    simpa only [d3234, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3234, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44357 p hg
    simpa only [d3234, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44359 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44354 p hg
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44344 p hg
    simpa only [d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44360 (p : Pattern) (guard : d8084 p = 1) : d3226 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1498 p hg
    simpa only [d8084, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44361 (p : Pattern) (guard : d8085 p = 1) : d3226 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44344 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44360 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44362 (p : Pattern) (guard : d8086 p = 1) : d3226 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44359 p hg
    simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44361 p hg
    simpa only [d8086, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44363 (p : Pattern) (guard : d8087 p = 1) : d3235 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d3235, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44358 p hg
    simpa only [d8087, d3235, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d3235, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44362 p hg
    simpa only [d8087, d3235, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44364 (p : Pattern) (guard : d8086 p = 1) : d3226 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44357 p hg
    simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44361 p hg
    simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44365 (p : Pattern) (guard : d8091 p = 1) : d3230 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3230, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44364 p hg
    simpa only [d8091, d3230, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3230, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d3230, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44366 (p : Pattern) (guard : d8092 p = 1) : d3236 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d3236, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44363 p hg
    simpa only [d8092, d3236, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d3236, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44365 p hg
    simpa only [d8092, d3236, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44367 (p : Pattern) (guard : d8093 p = 1) : d3237 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8088 p = 1 := by simpa only [d8093, d3237, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44352 p hg
    simpa only [d8093, d3237, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8092 p = 1 := by simpa only [d8093, d3237, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44366 p hg
    simpa only [d8093, d3237, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44368 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d339 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3226, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d3226, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3226, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3226, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44369 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44368 p hg
    simpa only [d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44344 p hg
    simpa only [d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44370 (p : Pattern) (guard : d1 p = 1) : d3226 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44369 p hg
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44359 p hg
    simpa only [d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44371 (p : Pattern) (guard : d8086 p = 1) : d3226 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44344 p hg
    simpa only [d8086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44361 p hg
    simpa only [d8086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44372 (p : Pattern) (guard : d8087 p = 1) : d3226 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44370 p hg
    simpa only [d8087, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44371 p hg
    simpa only [d8087, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44373 (p : Pattern) (guard : d8091 p = 1) : d3230 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3230, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44362 p hg
    simpa only [d8091, d3230, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3230, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d3230, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44374 (p : Pattern) (guard : d8092 p = 1) : d3238 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d3238, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44372 p hg
    simpa only [d8092, d3238, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d3238, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44373 p hg
    simpa only [d8092, d3238, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44375 (p : Pattern) (guard : d1 p = 1) : d3239 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3239, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34355 p hg
    simpa only [d3239, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3239, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3239, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44376 (p : Pattern) (guard : d1 p = 1) : d3239 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44377 (p : Pattern) (guard : d1 p = 1) : d3239 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44375 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44376 p hg
    simpa only [d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44378 (p : Pattern) (guard : d8084 p = 1) : d3239 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d8084, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44379 (p : Pattern) (guard : d8085 p = 1) : d3239 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44376 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44378 p hg
    simpa only [d8085, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
