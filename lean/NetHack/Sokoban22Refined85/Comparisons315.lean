/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons314
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare44100 (p : Pattern) (guard : d8117 p = 1) : d68 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d68, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44099 p hg
    simpa only [d8117, d68, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d68, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34899 p hg
    simpa only [d8117, d68, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44101 (p : Pattern) (guard : d8118 p = 1) : d1519 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1519, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44098 p hg
    simpa only [d8118, d1519, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1519, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44100 p hg
    simpa only [d8118, d1519, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44102 (p : Pattern) (guard : d8117 p = 1) : d71 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d71, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44071 p hg
    simpa only [d8117, d71, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d71, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34902 p hg
    simpa only [d8117, d71, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44103 (p : Pattern) (guard : d8123 p = 1) : d74 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d74, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44102 p hg
    simpa only [d8123, d74, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d74, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10096 p hg
    simpa only [d8123, d74, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44104 (p : Pattern) (guard : d8124 p = 1) : d1520 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1520, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44101 p hg
    simpa only [d8124, d1520, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1520, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44103 p hg
    simpa only [d8124, d1520, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44105 (p : Pattern) (guard : d8117 p = 1) : d1615 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34897 p hg
    simpa only [d8117, d1615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3627 p hg
    simpa only [d8117, d1615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44106 (p : Pattern) (guard : d8123 p = 1) : d1616 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44105 p hg
    simpa only [d8123, d1616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d8123, d1616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44107 (p : Pattern) (guard : d8129 p = 1) : d1617 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44106 p hg
    simpa only [d8129, d1617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13607 p hg
    simpa only [d8129, d1617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44108 (p : Pattern) (guard : d8130 p = 1) : d1618 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1618, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44104 p hg
    simpa only [d8130, d1618, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1618, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44107 p hg
    simpa only [d8130, d1618, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44109 (p : Pattern) (guard : d8131 p = 1) : d1619 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1619, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44095 p hg
    simpa only [d8131, d1619, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1619, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44108 p hg
    simpa only [d8131, d1619, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44110 (p : Pattern) (guard : d8112 p = 1) : d46 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43877 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35504 p hg
    simpa only [d8112, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44111 (p : Pattern) (guard : d8118 p = 1) : d1620 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1620, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44110 p hg
    simpa only [d8118, d1620, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1620, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41453 p hg
    simpa only [d8118, d1620, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44112 (p : Pattern) (guard : d8124 p = 1) : d1621 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1621, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44111 p hg
    simpa only [d8124, d1621, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1621, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41454 p hg
    simpa only [d8124, d1621, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44113 (p : Pattern) (guard : d0 p = 1) : d1622 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44114 (p : Pattern) (guard : d8117 p = 1) : d1623 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d8117, d1623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44113 p hg
    simpa only [d8117, d1623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44115 (p : Pattern) (guard : d8123 p = 1) : d1624 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44114 p hg
    simpa only [d8123, d1624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44116 (p : Pattern) (guard : d8129 p = 1) : d1625 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44115 p hg
    simpa only [d8129, d1625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44117 (p : Pattern) (guard : d8130 p = 1) : d1626 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1626, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44112 p hg
    simpa only [d8130, d1626, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1626, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44116 p hg
    simpa only [d8130, d1626, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44118 (p : Pattern) (guard : d8117 p = 1) : d66 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35610 p hg
    simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35532 p hg
    simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44119 (p : Pattern) (guard : d0 p = 1) : d1627 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare44120 (p : Pattern) (guard : d8123 p = 1) : d1628 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1628, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44118 p hg
    simpa only [d8123, d1628, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1628, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44119 p hg
    simpa only [d8123, d1628, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44121 (p : Pattern) (guard : d8129 p = 1) : d1629 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1629, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44120 p hg
    simpa only [d8129, d1629, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1629, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13607 p hg
    simpa only [d8129, d1629, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44122 (p : Pattern) (guard : d8135 p = 1) : d1633 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1633, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44121 p hg
    simpa only [d8135, d1633, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1633, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12036 p hg
    simpa only [d8135, d1633, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44123 (p : Pattern) (guard : d8136 p = 1) : d1634 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1634, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44117 p hg
    simpa only [d8136, d1634, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1634, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44122 p hg
    simpa only [d8136, d1634, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44124 (p : Pattern) (guard : d8137 p = 1) : d1635 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1635, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44109 p hg
    simpa only [d8137, d1635, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1635, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44123 p hg
    simpa only [d8137, d1635, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44125 (p : Pattern) (guard : d8111 p = 1) : d46 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d46, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35552 p hg
    simpa only [d8111, d46, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d46, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d46, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44126 (p : Pattern) (guard : d8112 p = 1) : d46 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44052 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44125 p hg
    simpa only [d8112, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44127 (p : Pattern) (guard : d8118 p = 1) : d1620 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1620, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44126 p hg
    simpa only [d8118, d1620, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1620, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41453 p hg
    simpa only [d8118, d1620, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44128 (p : Pattern) (guard : d8124 p = 1) : d1621 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1621, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44127 p hg
    simpa only [d8124, d1621, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1621, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41454 p hg
    simpa only [d8124, d1621, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44129 (p : Pattern) (guard : d8130 p = 1) : d1626 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1626, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44128 p hg
    simpa only [d8130, d1626, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1626, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44116 p hg
    simpa only [d8130, d1626, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44130 (p : Pattern) (guard : d8117 p = 1) : d66 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44069 p hg
    simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35532 p hg
    simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44131 (p : Pattern) (guard : d8123 p = 1) : d1628 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1628, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44130 p hg
    simpa only [d8123, d1628, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1628, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44119 p hg
    simpa only [d8123, d1628, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44132 (p : Pattern) (guard : d8129 p = 1) : d1629 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1629, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44131 p hg
    simpa only [d8129, d1629, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1629, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13607 p hg
    simpa only [d8129, d1629, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44133 (p : Pattern) (guard : d8135 p = 1) : d1633 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1633, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44132 p hg
    simpa only [d8135, d1633, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1633, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12036 p hg
    simpa only [d8135, d1633, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44134 (p : Pattern) (guard : d8136 p = 1) : d1634 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1634, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44129 p hg
    simpa only [d8136, d1634, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1634, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44133 p hg
    simpa only [d8136, d1634, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44135 (p : Pattern) (guard : d8142 p = 1) : d1636 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1636, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44134 p hg
    simpa only [d8142, d1636, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1636, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d1636, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44136 (p : Pattern) (guard : d8143 p = 1) : d1637 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d1637, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44124 p hg
    simpa only [d8143, d1637, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d1637, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44135 p hg
    simpa only [d8143, d1637, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44137 (p : Pattern) (guard : d8144 p = 1) : d1638 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d1638, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44086 p hg
    simpa only [d8144, d1638, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d1638, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44136 p hg
    simpa only [d8144, d1638, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44138 (p : Pattern) (guard : d8145 p = 1) : d1639 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d1639, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43885 p hg
    simpa only [d8145, d1639, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d1639, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44137 p hg
    simpa only [d8145, d1639, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44139 (p : Pattern) (guard : d8095 p = 1) : d324 p ≤ (0 : Int) + d324 p := by
  omega
theorem compare44140 (p : Pattern) (guard : d8096 p = 1) : d1504 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1504, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35564 p hg
    simpa only [d8096, d1504, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1504, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44139 p hg
    simpa only [d8096, d1504, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44141 (p : Pattern) (guard : d8102 p = 1) : d1506 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1506, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44140 p hg
    simpa only [d8102, d1506, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1506, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44034 p hg
    simpa only [d8102, d1506, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44142 (p : Pattern) (guard : d8107 p = 1) : d1508 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1508, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44024 p hg
    simpa only [d8107, d1508, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1508, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44037 p hg
    simpa only [d8107, d1508, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44143 (p : Pattern) (guard : d8108 p = 1) : d1509 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1509, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44141 p hg
    simpa only [d8108, d1509, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1509, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44142 p hg
    simpa only [d8108, d1509, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44144 (p : Pattern) (guard : d8112 p = 1) : d49 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d49, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43827 p hg
    simpa only [d8112, d49, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d49, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d49, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44145 (p : Pattern) (guard : d8113 p = 1) : d50 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d50, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44027 p hg
    simpa only [d8113, d50, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d50, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44144 p hg
    simpa only [d8113, d50, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44146 (p : Pattern) (guard : d8114 p = 1) : d1510 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1510, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44143 p hg
    simpa only [d8114, d1510, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1510, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44145 p hg
    simpa only [d8114, d1510, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44147 (p : Pattern) (guard : d8120 p = 1) : d1513 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1513, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44146 p hg
    simpa only [d8120, d1513, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1513, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44050 p hg
    simpa only [d8120, d1513, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44148 (p : Pattern) (guard : d8100 p = 1) : d359 p ≤ (0 : Int) + d359 p := by
  omega
theorem compare44149 (p : Pattern) (guard : d8101 p = 1) : d1514 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1514, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35585 p hg
    simpa only [d8101, d1514, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1514, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44148 p hg
    simpa only [d8101, d1514, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44150 (p : Pattern) (guard : d8106 p = 1) : d66 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d66, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35591 p hg
    simpa only [d8106, d66, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d66, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d66, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44151 (p : Pattern) (guard : d8107 p = 1) : d1515 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1515, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44149 p hg
    simpa only [d8107, d1515, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1515, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44150 p hg
    simpa only [d8107, d1515, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44152 (p : Pattern) (guard : d8106 p = 1) : d43 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d43, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35597 p hg
    simpa only [d8106, d43, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d43, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d43, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44153 (p : Pattern) (guard : d8111 p = 1) : d48 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d48, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35601 p hg
    simpa only [d8111, d48, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d48, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d48, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44154 (p : Pattern) (guard : d8112 p = 1) : d68 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d68, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44152 p hg
    simpa only [d8112, d68, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d68, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44153 p hg
    simpa only [d8112, d68, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44155 (p : Pattern) (guard : d8113 p = 1) : d1516 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1516, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44151 p hg
    simpa only [d8113, d1516, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1516, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44154 p hg
    simpa only [d8113, d1516, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44156 (p : Pattern) (guard : d8112 p = 1) : d71 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d71, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44037 p hg
    simpa only [d8112, d71, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d71, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43912 p hg
    simpa only [d8112, d71, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44157 (p : Pattern) (guard : d8117 p = 1) : d73 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d73, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43915 p hg
    simpa only [d8117, d73, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d73, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d73, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44158 (p : Pattern) (guard : d8118 p = 1) : d74 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d74, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44156 p hg
    simpa only [d8118, d74, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d74, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44157 p hg
    simpa only [d8118, d74, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44159 (p : Pattern) (guard : d8119 p = 1) : d1517 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1517, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44155 p hg
    simpa only [d8119, d1517, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1517, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44158 p hg
    simpa only [d8119, d1517, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44160 (p : Pattern) (guard : d8125 p = 1) : d1521 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1521, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44159 p hg
    simpa only [d8125, d1521, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1521, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44055 p hg
    simpa only [d8125, d1521, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44161 (p : Pattern) (guard : d8126 p = 1) : d1522 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1522, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44147 p hg
    simpa only [d8126, d1522, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1522, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44160 p hg
    simpa only [d8126, d1522, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44162 (p : Pattern) (guard : d8132 p = 1) : d1528 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1528, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44161 p hg
    simpa only [d8132, d1528, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1528, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44076 p hg
    simpa only [d8132, d1528, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44163 (p : Pattern) (guard : d8112 p = 1) : d176 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d176, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43741 p hg
    simpa only [d8112, d176, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d176, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43785 p hg
    simpa only [d8112, d176, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44164 (p : Pattern) (guard : d8118 p = 1) : d177 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d177, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44163 p hg
    simpa only [d8118, d177, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d177, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34691 p hg
    simpa only [d8118, d177, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44165 (p : Pattern) (guard : d8124 p = 1) : d1523 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1523, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44164 p hg
    simpa only [d8124, d1523, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1523, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1523, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44166 (p : Pattern) (guard : d8125 p = 1) : d1532 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1532, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44091 p hg
    simpa only [d8125, d1532, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1532, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44165 p hg
    simpa only [d8125, d1532, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44167 (p : Pattern) (guard : d8130 p = 1) : d1526 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1526, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44104 p hg
    simpa only [d8130, d1526, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1526, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43795 p hg
    simpa only [d8130, d1526, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44168 (p : Pattern) (guard : d8131 p = 1) : d1533 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1533, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44166 p hg
    simpa only [d8131, d1533, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1533, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44167 p hg
    simpa only [d8131, d1533, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44169 (p : Pattern) (guard : d8112 p = 1) : d1534 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1534, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43827 p hg
    simpa only [d8112, d1534, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1534, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34690 p hg
    simpa only [d8112, d1534, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44170 (p : Pattern) (guard : d8118 p = 1) : d1535 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1535, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44169 p hg
    simpa only [d8118, d1535, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1535, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34691 p hg
    simpa only [d8118, d1535, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44171 (p : Pattern) (guard : d8124 p = 1) : d1537 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1537, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44170 p hg
    simpa only [d8124, d1537, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1537, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44079 p hg
    simpa only [d8124, d1537, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44172 (p : Pattern) (guard : d8130 p = 1) : d1539 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1539, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44171 p hg
    simpa only [d8130, d1539, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1539, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44081 p hg
    simpa only [d8130, d1539, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44173 (p : Pattern) (guard : d8123 p = 1) : d1536 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1536, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44157 p hg
    simpa only [d8123, d1536, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1536, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1536, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44174 (p : Pattern) (guard : d8129 p = 1) : d1538 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1538, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44173 p hg
    simpa only [d8129, d1538, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1538, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1538, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44175 (p : Pattern) (guard : d8135 p = 1) : d1540 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1540, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44174 p hg
    simpa only [d8135, d1540, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1540, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d1540, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44176 (p : Pattern) (guard : d8136 p = 1) : d1541 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1541, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44172 p hg
    simpa only [d8136, d1541, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1541, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44175 p hg
    simpa only [d8136, d1541, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44177 (p : Pattern) (guard : d8137 p = 1) : d1542 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1542, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44168 p hg
    simpa only [d8137, d1542, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1542, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44176 p hg
    simpa only [d8137, d1542, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44178 (p : Pattern) (guard : d8138 p = 1) : d1543 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1543, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44162 p hg
    simpa only [d8138, d1543, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1543, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44177 p hg
    simpa only [d8138, d1543, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44179 (p : Pattern) (guard : d8107 p = 1) : d1544 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1544, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44034 p hg
    simpa only [d8107, d1544, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1544, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44096 p hg
    simpa only [d8107, d1544, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44180 (p : Pattern) (guard : d8112 p = 1) : d47 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d47, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44068 p hg
    simpa only [d8112, d47, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d47, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44099 p hg
    simpa only [d8112, d47, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44181 (p : Pattern) (guard : d8113 p = 1) : d1545 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1545, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44179 p hg
    simpa only [d8113, d1545, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1545, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44180 p hg
    simpa only [d8113, d1545, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44182 (p : Pattern) (guard : d8118 p = 1) : d50 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d50, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44088 p hg
    simpa only [d8118, d50, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d50, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34871 p hg
    simpa only [d8118, d50, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44183 (p : Pattern) (guard : d8119 p = 1) : d1546 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1546, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44181 p hg
    simpa only [d8119, d1546, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1546, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44182 p hg
    simpa only [d8119, d1546, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44184 (p : Pattern) (guard : d8118 p = 1) : d1511 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1511, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44110 p hg
    simpa only [d8118, d1511, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1511, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35505 p hg
    simpa only [d8118, d1511, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44185 (p : Pattern) (guard : d8124 p = 1) : d1512 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1512, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44184 p hg
    simpa only [d8124, d1512, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1512, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35506 p hg
    simpa only [d8124, d1512, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44186 (p : Pattern) (guard : d8125 p = 1) : d1547 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1547, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44183 p hg
    simpa only [d8125, d1547, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1547, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44185 p hg
    simpa only [d8125, d1547, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44187 (p : Pattern) (guard : d8106 p = 1) : d46 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d46, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35652 p hg
    simpa only [d8106, d46, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d46, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d46, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44188 (p : Pattern) (guard : d8111 p = 1) : d66 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d66, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35658 p hg
    simpa only [d8111, d66, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d66, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d66, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44189 (p : Pattern) (guard : d8112 p = 1) : d1518 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1518, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44187 p hg
    simpa only [d8112, d1518, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1518, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44188 p hg
    simpa only [d8112, d1518, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44190 (p : Pattern) (guard : d8111 p = 1) : d43 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d43, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35665 p hg
    simpa only [d8111, d43, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d43, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d43, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44191 (p : Pattern) (guard : d8117 p = 1) : d68 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d68, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44190 p hg
    simpa only [d8117, d68, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d68, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34899 p hg
    simpa only [d8117, d68, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44192 (p : Pattern) (guard : d8118 p = 1) : d1519 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1519, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44189 p hg
    simpa only [d8118, d1519, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1519, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44191 p hg
    simpa only [d8118, d1519, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44193 (p : Pattern) (guard : d8117 p = 1) : d71 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d71, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44099 p hg
    simpa only [d8117, d71, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d71, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34902 p hg
    simpa only [d8117, d71, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44194 (p : Pattern) (guard : d8123 p = 1) : d74 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d74, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44193 p hg
    simpa only [d8123, d74, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d74, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10096 p hg
    simpa only [d8123, d74, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44195 (p : Pattern) (guard : d8124 p = 1) : d1520 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1520, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44192 p hg
    simpa only [d8124, d1520, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1520, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44194 p hg
    simpa only [d8124, d1520, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44196 (p : Pattern) (guard : d8117 p = 1) : d1518 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1518, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44125 p hg
    simpa only [d8117, d1518, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1518, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35532 p hg
    simpa only [d8117, d1518, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44197 (p : Pattern) (guard : d8123 p = 1) : d1519 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1519, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44196 p hg
    simpa only [d8123, d1519, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1519, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35534 p hg
    simpa only [d8123, d1519, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44198 (p : Pattern) (guard : d8129 p = 1) : d1520 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1520, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44197 p hg
    simpa only [d8129, d1520, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1520, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13494 p hg
    simpa only [d8129, d1520, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44199 (p : Pattern) (guard : d8130 p = 1) : d1520 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44195 p hg
    simpa only [d8130, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44198 p hg
    simpa only [d8130, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44200 (p : Pattern) (guard : d8131 p = 1) : d1548 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1548, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44186 p hg
    simpa only [d8131, d1548, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1548, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44199 p hg
    simpa only [d8131, d1548, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44201 (p : Pattern) (guard : d8118 p = 1) : d1511 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1511, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44126 p hg
    simpa only [d8118, d1511, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1511, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35505 p hg
    simpa only [d8118, d1511, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44202 (p : Pattern) (guard : d8124 p = 1) : d1512 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1512, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44201 p hg
    simpa only [d8124, d1512, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1512, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35506 p hg
    simpa only [d8124, d1512, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44203 (p : Pattern) (guard : d8129 p = 1) : d1523 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41454 p hg
    simpa only [d8129, d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44204 (p : Pattern) (guard : d8130 p = 1) : d1524 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1524, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44202 p hg
    simpa only [d8130, d1524, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1524, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44203 p hg
    simpa only [d8130, d1524, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44205 (p : Pattern) (guard : d8111 p = 1) : d46 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d46, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35685 p hg
    simpa only [d8111, d46, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d46, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d46, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44206 (p : Pattern) (guard : d8117 p = 1) : d1518 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1518, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44205 p hg
    simpa only [d8117, d1518, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1518, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35532 p hg
    simpa only [d8117, d1518, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44207 (p : Pattern) (guard : d8123 p = 1) : d1519 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1519, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44206 p hg
    simpa only [d8123, d1519, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1519, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35534 p hg
    simpa only [d8123, d1519, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44208 (p : Pattern) (guard : d8129 p = 1) : d1520 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1520, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44207 p hg
    simpa only [d8129, d1520, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1520, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13494 p hg
    simpa only [d8129, d1520, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44209 (p : Pattern) (guard : d8135 p = 1) : d1526 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1526, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44208 p hg
    simpa only [d8135, d1526, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1526, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11898 p hg
    simpa only [d8135, d1526, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44210 (p : Pattern) (guard : d8136 p = 1) : d1527 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1527, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44204 p hg
    simpa only [d8136, d1527, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1527, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44209 p hg
    simpa only [d8136, d1527, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44211 (p : Pattern) (guard : d8137 p = 1) : d1549 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1549, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44200 p hg
    simpa only [d8137, d1549, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1549, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44210 p hg
    simpa only [d8137, d1549, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44212 (p : Pattern) (guard : d8112 p = 1) : d46 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44068 p hg
    simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44205 p hg
    simpa only [d8112, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44213 (p : Pattern) (guard : d8117 p = 1) : d47 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d47, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44125 p hg
    simpa only [d8117, d47, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d47, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3627 p hg
    simpa only [d8117, d47, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44214 (p : Pattern) (guard : d8118 p = 1) : d1511 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1511, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44212 p hg
    simpa only [d8118, d1511, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1511, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44213 p hg
    simpa only [d8118, d1511, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44215 (p : Pattern) (guard : d8124 p = 1) : d1512 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1512, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44214 p hg
    simpa only [d8124, d1512, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1512, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35506 p hg
    simpa only [d8124, d1512, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44216 (p : Pattern) (guard : d8130 p = 1) : d1524 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1524, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44215 p hg
    simpa only [d8130, d1524, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1524, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44203 p hg
    simpa only [d8130, d1524, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44217 (p : Pattern) (guard : d8111 p = 1) : d46 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d46, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41496 p hg
    simpa only [d8111, d46, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d46, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d46, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44218 (p : Pattern) (guard : d8117 p = 1) : d1518 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1518, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44217 p hg
    simpa only [d8117, d1518, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1518, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35532 p hg
    simpa only [d8117, d1518, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44219 (p : Pattern) (guard : d8123 p = 1) : d1519 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1519, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44218 p hg
    simpa only [d8123, d1519, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1519, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35534 p hg
    simpa only [d8123, d1519, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44220 (p : Pattern) (guard : d8129 p = 1) : d1520 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1520, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44219 p hg
    simpa only [d8129, d1520, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1520, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13494 p hg
    simpa only [d8129, d1520, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44221 (p : Pattern) (guard : d8135 p = 1) : d1526 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1526, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44220 p hg
    simpa only [d8135, d1526, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1526, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11898 p hg
    simpa only [d8135, d1526, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44222 (p : Pattern) (guard : d8136 p = 1) : d1527 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1527, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44216 p hg
    simpa only [d8136, d1527, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1527, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44221 p hg
    simpa only [d8136, d1527, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44223 (p : Pattern) (guard : d8142 p = 1) : d1550 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1550, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44222 p hg
    simpa only [d8142, d1550, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1550, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d1550, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44224 (p : Pattern) (guard : d8143 p = 1) : d1551 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d1551, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44211 p hg
    simpa only [d8143, d1551, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d1551, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44223 p hg
    simpa only [d8143, d1551, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44225 (p : Pattern) (guard : d8144 p = 1) : d1552 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d1552, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44178 p hg
    simpa only [d8144, d1552, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d1552, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44224 p hg
    simpa only [d8144, d1552, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44226 (p : Pattern) (guard : d8100 p = 1) : d353 p ≤ (0 : Int) + d353 p := by
  omega
theorem compare44227 (p : Pattern) (guard : d8101 p = 1) : d1572 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1572, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35698 p hg
    simpa only [d8101, d1572, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1572, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44226 p hg
    simpa only [d8101, d1572, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44228 (p : Pattern) (guard : d8105 p = 1) : d343 p ≤ (0 : Int) + d343 p := by
  omega
theorem compare44229 (p : Pattern) (guard : d8106 p = 1) : d1573 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1573, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35704 p hg
    simpa only [d8106, d1573, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1573, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44228 p hg
    simpa only [d8106, d1573, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44230 (p : Pattern) (guard : d8107 p = 1) : d1574 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1574, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44227 p hg
    simpa only [d8107, d1574, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1574, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44229 p hg
    simpa only [d8107, d1574, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44231 (p : Pattern) (guard : d8106 p = 1) : d124 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d124, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35711 p hg
    simpa only [d8106, d124, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d124, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d124, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44232 (p : Pattern) (guard : d8111 p = 1) : d125 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d125, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35717 p hg
    simpa only [d8111, d125, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d125, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d125, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44233 (p : Pattern) (guard : d8112 p = 1) : d126 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d126, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44231 p hg
    simpa only [d8112, d126, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d126, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44232 p hg
    simpa only [d8112, d126, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44234 (p : Pattern) (guard : d8113 p = 1) : d1575 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1575, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44230 p hg
    simpa only [d8113, d1575, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1575, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44233 p hg
    simpa only [d8113, d1575, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44235 (p : Pattern) (guard : d8111 p = 1) : d125 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d125, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35725 p hg
    simpa only [d8111, d125, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d125, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d125, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44236 (p : Pattern) (guard : d8112 p = 1) : d126 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d126, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43981 p hg
    simpa only [d8112, d126, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d126, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44235 p hg
    simpa only [d8112, d126, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44237 (p : Pattern) (guard : d8117 p = 1) : d128 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d128, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43912 p hg
    simpa only [d8117, d128, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d128, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d128, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44238 (p : Pattern) (guard : d8118 p = 1) : d129 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d129, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44236 p hg
    simpa only [d8118, d129, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d129, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44237 p hg
    simpa only [d8118, d129, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44239 (p : Pattern) (guard : d8119 p = 1) : d1576 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1576, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44234 p hg
    simpa only [d8119, d1576, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1576, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44238 p hg
    simpa only [d8119, d1576, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
