/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons114
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare16100 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (2 : Int) + d18 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16101 (p : Pattern) (guard : d1 p = 1) : d1775 p ≤ (2 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4694 p hg
    simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4697 p hg
    simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16102 (p : Pattern) (guard : d1 p = 1) : d1776 p ≤ (2 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1776, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16101 p hg
    simpa only [d1776, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1776, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4698 p hg
    simpa only [d1776, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16103 (p : Pattern) (guard : d1 p = 1) : d1777 p ≤ (2 : Int) + d18 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4696 p hg
    simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16102 p hg
    simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16104 (p : Pattern) (guard : d1 p = 1) : d1769 p ≤ (2 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4694 p hg
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15683 p hg
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16105 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (2 : Int) + d17 p := by
  omega
theorem compare16106 (p : Pattern) (guard : d1 p = 1) : d1770 p ≤ (2 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1770, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16104 p hg
    simpa only [d1770, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1770, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16105 p hg
    simpa only [d1770, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16107 (p : Pattern) (guard : d1 p = 1) : d2047 p ≤ (2 : Int) + d18 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16106 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16102 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16108 (p : Pattern) (guard : d1 p = 1) : d2048 p ≤ (2 : Int) + d18 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16103 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16107 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16109 (p : Pattern) (guard : d4474 p = 1) : d2049 p ≤ (2 : Int) + d18 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16108 p hg
    simpa only [d4474, d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15688 p hg
    simpa only [d4474, d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16110 (p : Pattern) (guard : d4475 p = 1) : d2050 p ≤ (2 : Int) + d18 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16100 p hg
    simpa only [d4475, d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16109 p hg
    simpa only [d4475, d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16111 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (2 : Int) + d191 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16112 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d8 p := by
  change (0 : Int) ≤ (2 : Int) + 8
  decide
theorem compare16113 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (2 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16112 p hg
    simpa only [d13, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d13, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16114 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (2 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16112 p hg
    simpa only [d14, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16113 p hg
    simpa only [d14, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16115 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (2 : Int) + d8 p := by
  change (6 : Int) ≤ (2 : Int) + 8
  decide
theorem compare16116 (p : Pattern) (guard : d1 p = 1) : d1775 p ≤ (2 : Int) + d8 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16112 p hg
    simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16115 p hg
    simpa only [d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16117 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (2 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16115 p hg
    simpa only [d34, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d34, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16118 (p : Pattern) (guard : d1 p = 1) : d1776 p ≤ (2 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1776, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16116 p hg
    simpa only [d1776, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1776, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16117 p hg
    simpa only [d1776, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16119 (p : Pattern) (guard : d1 p = 1) : d1777 p ≤ (2 : Int) + d191 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16114 p hg
    simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16118 p hg
    simpa only [d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16120 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d8 p := by
  change (4 : Int) ≤ (2 : Int) + 8
  decide
theorem compare16121 (p : Pattern) (guard : d1 p = 1) : d1769 p ≤ (2 : Int) + d8 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16112 p hg
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16120 p hg
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16122 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (2 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16120 p hg
    simpa only [d17, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d17, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16123 (p : Pattern) (guard : d1 p = 1) : d1770 p ≤ (2 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1770, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16121 p hg
    simpa only [d1770, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1770, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16122 p hg
    simpa only [d1770, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16124 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (2 : Int) + d8 p := by
  change (10 : Int) ≤ (2 : Int) + 8
  decide
theorem compare16125 (p : Pattern) (guard : d1 p = 1) : d2051 p ≤ (2 : Int) + d8 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16112 p hg
    simpa only [d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16124 p hg
    simpa only [d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16126 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (2 : Int) + d8 p := by
  change (9 : Int) ≤ (2 : Int) + 8
  decide
theorem compare16127 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (2 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16126 p hg
    simpa only [d23, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d23, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16128 (p : Pattern) (guard : d1 p = 1) : d2052 p ≤ (2 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2052, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16125 p hg
    simpa only [d2052, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2052, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16127 p hg
    simpa only [d2052, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16129 (p : Pattern) (guard : d1 p = 1) : d2053 p ≤ (2 : Int) + d191 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16123 p hg
    simpa only [d2053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16128 p hg
    simpa only [d2053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16130 (p : Pattern) (guard : d1 p = 1) : d2054 p ≤ (2 : Int) + d191 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16119 p hg
    simpa only [d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16129 p hg
    simpa only [d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16131 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d191 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16132 (p : Pattern) (guard : d4474 p = 1) : d2055 p ≤ (2 : Int) + d191 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16130 p hg
    simpa only [d4474, d2055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16131 p hg
    simpa only [d4474, d2055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16133 (p : Pattern) (guard : d4475 p = 1) : d2056 p ≤ (2 : Int) + d191 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d2056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16111 p hg
    simpa only [d4475, d2056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d2056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16132 p hg
    simpa only [d4475, d2056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16134 (p : Pattern) (guard : d4475 p = 1) : d2057 p ≤ (2 : Int) + d4557 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2057, d4557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16110 p hg
    simpa only [d2057, d4557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2057, d4557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16133 p hg
    simpa only [d2057, d4557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16135 (p : Pattern) (guard : d0 p = 1) : d36 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16136 (p : Pattern) (guard : d1 p = 1) : d364 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4841 p hg
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16137 (p : Pattern) (guard : d1 p = 1) : d1720 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4842 p hg
    simpa only [d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16136 p hg
    simpa only [d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16138 (p : Pattern) (guard : d1 p = 1) : d1721 p ≤ (2 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4840 p hg
    simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1829 p hg
    simpa only [d1721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16139 (p : Pattern) (guard : d1 p = 1) : d1722 p ≤ (2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16138 p hg
    simpa only [d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1830 p hg
    simpa only [d1722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16140 (p : Pattern) (guard : d1 p = 1) : d1723 p ≤ (2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16139 p hg
    simpa only [d1723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16136 p hg
    simpa only [d1723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16141 (p : Pattern) (guard : d1 p = 1) : d1724 p ≤ (2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16137 p hg
    simpa only [d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16140 p hg
    simpa only [d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16142 (p : Pattern) (guard : d4474 p = 1) : d1725 p ≤ (2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16141 p hg
    simpa only [d4474, d1725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6043 p hg
    simpa only [d4474, d1725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16143 (p : Pattern) (guard : d4475 p = 1) : d1810 p ≤ (2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16135 p hg
    simpa only [d4475, d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16142 p hg
    simpa only [d4475, d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16144 (p : Pattern) (guard : d4475 p = 1) : d1811 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15842 p hg
    simpa only [d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16143 p hg
    simpa only [d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16145 (p : Pattern) (guard : d4475 p = 1) : d2058 p ≤ (2 : Int) + d4558 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2058, d4558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16134 p hg
    simpa only [d2058, d4558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2058, d4558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16144 p hg
    simpa only [d2058, d4558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16146 (p : Pattern) (guard : d4475 p = 1) : d1812 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16144 p hg
    simpa only [d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15859 p hg
    simpa only [d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16147 (p : Pattern) (guard : d4475 p = 1) : d2059 p ≤ (2 : Int) + d4559 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2059, d4559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16145 p hg
    simpa only [d2059, d4559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2059, d4559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16146 p hg
    simpa only [d2059, d4559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16148 (p : Pattern) (guard : d0 p = 1) : d2066 p ≤ (2 : Int) + d4559 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16149 (p : Pattern) (guard : d4476 p = 1) : d2067 p ≤ (2 : Int) + d4559 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d2067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16147 p hg
    simpa only [d4476, d2067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d2067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16148 p hg
    simpa only [d4476, d2067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16150 (p : Pattern) (guard : d0 p = 1) : d32 p ≤ (2 : Int) + d191 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16151 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d8 p := by
  change (2 : Int) ≤ (2 : Int) + 8
  decide
theorem compare16152 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (2 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16151 p hg
    simpa only [d30, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d30, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16153 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (2 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16151 p hg
    simpa only [d31, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16152 p hg
    simpa only [d31, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16154 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (2 : Int) + d8 p := by
  omega
theorem compare16155 (p : Pattern) (guard : d1 p = 1) : d1710 p ≤ (2 : Int) + d8 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16151 p hg
    simpa only [d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16154 p hg
    simpa only [d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16156 (p : Pattern) (guard : d1 p = 1) : d190 p ≤ (2 : Int) + d190 p := by
  omega
theorem compare16157 (p : Pattern) (guard : d1 p = 1) : d1711 p ≤ (2 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1711, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16155 p hg
    simpa only [d1711, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1711, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16156 p hg
    simpa only [d1711, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16158 (p : Pattern) (guard : d1 p = 1) : d1712 p ≤ (2 : Int) + d191 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16153 p hg
    simpa only [d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16157 p hg
    simpa only [d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16159 (p : Pattern) (guard : d1 p = 1) : d1713 p ≤ (2 : Int) + d8 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16151 p hg
    simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16115 p hg
    simpa only [d1713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16160 (p : Pattern) (guard : d1 p = 1) : d1714 p ≤ (2 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1714, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16159 p hg
    simpa only [d1714, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1714, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16117 p hg
    simpa only [d1714, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16161 (p : Pattern) (guard : d1 p = 1) : d2068 p ≤ (2 : Int) + d8 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16151 p hg
    simpa only [d2068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16124 p hg
    simpa only [d2068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16162 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (2 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16124 p hg
    simpa only [d57, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d57, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16163 (p : Pattern) (guard : d1 p = 1) : d2069 p ≤ (2 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2069, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16161 p hg
    simpa only [d2069, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2069, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16162 p hg
    simpa only [d2069, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16164 (p : Pattern) (guard : d1 p = 1) : d2070 p ≤ (2 : Int) + d191 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16160 p hg
    simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16163 p hg
    simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16165 (p : Pattern) (guard : d1 p = 1) : d2071 p ≤ (2 : Int) + d191 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16158 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16164 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16166 (p : Pattern) (guard : d4474 p = 1) : d2072 p ≤ (2 : Int) + d191 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16165 p hg
    simpa only [d4474, d2072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16131 p hg
    simpa only [d4474, d2072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16167 (p : Pattern) (guard : d4475 p = 1) : d2073 p ≤ (2 : Int) + d191 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16150 p hg
    simpa only [d4475, d2073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16166 p hg
    simpa only [d4475, d2073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16168 (p : Pattern) (guard : d4475 p = 1) : d2074 p ≤ (2 : Int) + d4564 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2074, d4564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16167 p hg
    simpa only [d2074, d4564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2074, d4564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15842 p hg
    simpa only [d2074, d4564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16169 (p : Pattern) (guard : d4475 p = 1) : d2075 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15802 p hg
    simpa only [d2075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15858 p hg
    simpa only [d2075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16170 (p : Pattern) (guard : d4475 p = 1) : d2076 p ≤ (2 : Int) + d4565 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2076, d4565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16168 p hg
    simpa only [d2076, d4565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2076, d4565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16169 p hg
    simpa only [d2076, d4565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16171 (p : Pattern) (guard : d4475 p = 1) : d1821 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16143 p hg
    simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16172 (p : Pattern) (guard : d4475 p = 1) : d1822 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16171 p hg
    simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d1822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16173 (p : Pattern) (guard : d4475 p = 1) : d2077 p ≤ (2 : Int) + d4566 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2077, d4566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16170 p hg
    simpa only [d2077, d4566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2077, d4566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16172 p hg
    simpa only [d2077, d4566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16174 (p : Pattern) (guard : d0 p = 1) : d2080 p ≤ (2 : Int) + d4566 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16175 (p : Pattern) (guard : d4476 p = 1) : d2081 p ≤ (2 : Int) + d4566 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d2081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16173 p hg
    simpa only [d4476, d2081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d2081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16174 p hg
    simpa only [d4476, d2081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16176 (p : Pattern) (guard : d4476 p = 1) : d2082 p ≤ (2 : Int) + d5519 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2082, d5519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16149 p hg
    simpa only [d2082, d5519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2082, d5519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16175 p hg
    simpa only [d2082, d5519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16177 (p : Pattern) (guard : d4476 p = 1) : d2083 p ≤ (2 : Int) + d5520 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2083, d5520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16099 p hg
    simpa only [d2083, d5520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2083, d5520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16176 p hg
    simpa only [d2083, d5520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16178 (p : Pattern) (guard : d4476 p = 1) : d2084 p ≤ (2 : Int) + d5521 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2084, d5521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16176 p hg
    simpa only [d2084, d5521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2084, d5521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15895 p hg
    simpa only [d2084, d5521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16179 (p : Pattern) (guard : d4476 p = 1) : d2085 p ≤ (2 : Int) + d5522 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2085, d5522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16177 p hg
    simpa only [d2085, d5522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2085, d5522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16178 p hg
    simpa only [d2085, d5522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16180 (p : Pattern) (guard : d4476 p = 1) : d2086 p ≤ (2 : Int) + d5523 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2086, d5523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15911 p hg
    simpa only [d2086, d5523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2086, d5523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16179 p hg
    simpa only [d2086, d5523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16181 (p : Pattern) (guard : d4476 p = 1) : d2087 p ≤ (2 : Int) + d5524 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2087, d5524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15898 p hg
    simpa only [d2087, d5524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2087, d5524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16180 p hg
    simpa only [d2087, d5524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16182 (p : Pattern) (guard : d4475 p = 1) : d2088 p ≤ (2 : Int) + d4574 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2088, d4574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15940 p hg
    simpa only [d2088, d4574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2088, d4574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d2088, d4574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16183 (p : Pattern) (guard : d4475 p = 1) : d2089 p ≤ (2 : Int) + d4575 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2089, d4575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15959 p hg
    simpa only [d2089, d4575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2089, d4575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16182 p hg
    simpa only [d2089, d4575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16184 (p : Pattern) (guard : d4475 p = 1) : d2090 p ≤ (2 : Int) + d4576 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2090, d4576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16182 p hg
    simpa only [d2090, d4576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2090, d4576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d2090, d4576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16185 (p : Pattern) (guard : d4475 p = 1) : d2091 p ≤ (2 : Int) + d4577 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2091, d4577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16183 p hg
    simpa only [d2091, d4577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2091, d4577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16184 p hg
    simpa only [d2091, d4577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16186 (p : Pattern) (guard : d0 p = 1) : d2095 p ≤ (2 : Int) + d4577 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16187 (p : Pattern) (guard : d4476 p = 1) : d2096 p ≤ (2 : Int) + d4577 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16185 p hg
    simpa only [d4476, d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16186 p hg
    simpa only [d4476, d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16188 (p : Pattern) (guard : d4476 p = 1) : d2097 p ≤ (2 : Int) + d4578 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2097, d4578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15947 p hg
    simpa only [d2097, d4578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2097, d4578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16187 p hg
    simpa only [d2097, d4578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16189 (p : Pattern) (guard : d4475 p = 1) : d2098 p ≤ (2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16020 p hg
    simpa only [d2098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d2098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16190 (p : Pattern) (guard : d4475 p = 1) : d2099 p ≤ (2 : Int) + d4530 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2099, d4530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16039 p hg
    simpa only [d2099, d4530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2099, d4530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16189 p hg
    simpa only [d2099, d4530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16191 (p : Pattern) (guard : d4475 p = 1) : d2100 p ≤ (2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16189 p hg
    simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16192 (p : Pattern) (guard : d4475 p = 1) : d2101 p ≤ (2 : Int) + d4531 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2101, d4531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16190 p hg
    simpa only [d2101, d4531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2101, d4531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16191 p hg
    simpa only [d2101, d4531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16193 (p : Pattern) (guard : d4476 p = 1) : d2102 p ≤ (2 : Int) + d4531 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d2102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16192 p hg
    simpa only [d4476, d2102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d2102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16045 p hg
    simpa only [d4476, d2102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16194 (p : Pattern) (guard : d4476 p = 1) : d2103 p ≤ (2 : Int) + d5512 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2103, d5512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16027 p hg
    simpa only [d2103, d5512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2103, d5512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16193 p hg
    simpa only [d2103, d5512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16195 (p : Pattern) (guard : d4476 p = 1) : d2104 p ≤ (2 : Int) + d5525 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2104, d5525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16188 p hg
    simpa only [d2104, d5525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2104, d5525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16194 p hg
    simpa only [d2104, d5525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16196 (p : Pattern) (guard : d4476 p = 1) : d2105 p ≤ (2 : Int) + d5514 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2105, d5514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16194 p hg
    simpa only [d2105, d5514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2105, d5514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16052 p hg
    simpa only [d2105, d5514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16197 (p : Pattern) (guard : d4476 p = 1) : d2106 p ≤ (2 : Int) + d5526 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d2106, d5526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16195 p hg
    simpa only [d2106, d5526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d2106, d5526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16196 p hg
    simpa only [d2106, d5526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16198 (p : Pattern) (guard : d0 p = 1) : d104 p ≤ (2 : Int) + d107 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16199 (p : Pattern) (guard : d1 p = 1) : d1945 p ≤ (2 : Int) + d5 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4776 p hg
    simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2168 p hg
    simpa only [d1945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16200 (p : Pattern) (guard : d1 p = 1) : d1946 p ≤ (2 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1946, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16199 p hg
    simpa only [d1946, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1946, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2169 p hg
    simpa only [d1946, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16201 (p : Pattern) (guard : d1 p = 1) : d1947 p ≤ (2 : Int) + d107 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4778 p hg
    simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16200 p hg
    simpa only [d1947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16202 (p : Pattern) (guard : d1 p = 1) : d1939 p ≤ (2 : Int) + d5 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4776 p hg
    simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15933 p hg
    simpa only [d1939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16203 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (2 : Int) + d106 p := by
  omega
theorem compare16204 (p : Pattern) (guard : d1 p = 1) : d1940 p ≤ (2 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1940, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16202 p hg
    simpa only [d1940, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1940, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16203 p hg
    simpa only [d1940, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16205 (p : Pattern) (guard : d1 p = 1) : d2107 p ≤ (2 : Int) + d107 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16204 p hg
    simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16200 p hg
    simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16206 (p : Pattern) (guard : d1 p = 1) : d2108 p ≤ (2 : Int) + d107 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16201 p hg
    simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16205 p hg
    simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16207 (p : Pattern) (guard : d4474 p = 1) : d2109 p ≤ (2 : Int) + d107 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16206 p hg
    simpa only [d4474, d2109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15938 p hg
    simpa only [d4474, d2109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16208 (p : Pattern) (guard : d4475 p = 1) : d2110 p ≤ (2 : Int) + d107 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d2110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16198 p hg
    simpa only [d4475, d2110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d2110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16207 p hg
    simpa only [d4475, d2110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16209 (p : Pattern) (guard : d4475 p = 1) : d2111 p ≤ (2 : Int) + d4574 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2111, d4574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16208 p hg
    simpa only [d2111, d4574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2111, d4574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16020 p hg
    simpa only [d2111, d4574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16210 (p : Pattern) (guard : d4475 p = 1) : d2112 p ≤ (2 : Int) + d4584 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2112, d4584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15974 p hg
    simpa only [d2112, d4584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2112, d4584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16209 p hg
    simpa only [d2112, d4584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16211 (p : Pattern) (guard : d4475 p = 1) : d2113 p ≤ (2 : Int) + d4529 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2113, d4529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15994 p hg
    simpa only [d2113, d4529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2113, d4529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16020 p hg
    simpa only [d2113, d4529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16212 (p : Pattern) (guard : d4475 p = 1) : d2114 p ≤ (2 : Int) + d4530 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2114, d4530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16211 p hg
    simpa only [d2114, d4530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2114, d4530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16023 p hg
    simpa only [d2114, d4530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16213 (p : Pattern) (guard : d4475 p = 1) : d2115 p ≤ (2 : Int) + d4585 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2115, d4585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16210 p hg
    simpa only [d2115, d4585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2115, d4585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16212 p hg
    simpa only [d2115, d4585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16214 (p : Pattern) (guard : d0 p = 1) : d2122 p ≤ (2 : Int) + d4585 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16215 (p : Pattern) (guard : d4476 p = 1) : d2123 p ≤ (2 : Int) + d4585 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d2123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16213 p hg
    simpa only [d4476, d2123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d2123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16214 p hg
    simpa only [d4476, d2123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16216 (p : Pattern) (guard : d0 p = 1) : d117 p ≤ (2 : Int) + d107 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16217 (p : Pattern) (guard : d1 p = 1) : d1894 p ≤ (2 : Int) + d5 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4913 p hg
    simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2168 p hg
    simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16218 (p : Pattern) (guard : d1 p = 1) : d1895 p ≤ (2 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1895, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16217 p hg
    simpa only [d1895, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1895, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2169 p hg
    simpa only [d1895, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16219 (p : Pattern) (guard : d1 p = 1) : d2124 p ≤ (2 : Int) + d107 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4915 p hg
    simpa only [d2124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16218 p hg
    simpa only [d2124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16220 (p : Pattern) (guard : d1 p = 1) : d2125 p ≤ (2 : Int) + d107 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16219 p hg
    simpa only [d2125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16218 p hg
    simpa only [d2125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16221 (p : Pattern) (guard : d4474 p = 1) : d2126 p ≤ (2 : Int) + d107 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16220 p hg
    simpa only [d4474, d2126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15938 p hg
    simpa only [d4474, d2126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16222 (p : Pattern) (guard : d4475 p = 1) : d2127 p ≤ (2 : Int) + d107 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d2127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16216 p hg
    simpa only [d4475, d2127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d2127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16221 p hg
    simpa only [d4475, d2127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16223 (p : Pattern) (guard : d4475 p = 1) : d2128 p ≤ (2 : Int) + d107 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16208 p hg
    simpa only [d2128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16222 p hg
    simpa only [d2128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16224 (p : Pattern) (guard : d0 p = 1) : d108 p ≤ (2 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16225 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (2 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15984 p hg
    simpa only [d107, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15986 p hg
    simpa only [d107, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16226 (p : Pattern) (guard : d1 p = 1) : d1963 p ≤ (2 : Int) + d7 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15984 p hg
    simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4942 p hg
    simpa only [d1963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16227 (p : Pattern) (guard : d1 p = 1) : d1964 p ≤ (2 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1964, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16226 p hg
    simpa only [d1964, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1964, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4943 p hg
    simpa only [d1964, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16228 (p : Pattern) (guard : d1 p = 1) : d2129 p ≤ (2 : Int) + d120 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16225 p hg
    simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16227 p hg
    simpa only [d2129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16229 (p : Pattern) (guard : d1 p = 1) : d2130 p ≤ (2 : Int) + d120 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16228 p hg
    simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16227 p hg
    simpa only [d2130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16230 (p : Pattern) (guard : d4474 p = 1) : d2131 p ≤ (2 : Int) + d120 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16229 p hg
    simpa only [d4474, d2131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15992 p hg
    simpa only [d4474, d2131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16231 (p : Pattern) (guard : d4475 p = 1) : d2132 p ≤ (2 : Int) + d120 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d2132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16224 p hg
    simpa only [d4475, d2132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d2132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16230 p hg
    simpa only [d4475, d2132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16232 (p : Pattern) (guard : d4475 p = 1) : d2133 p ≤ (2 : Int) + d4529 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2133, d4529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16231 p hg
    simpa only [d2133, d4529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2133, d4529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15702 p hg
    simpa only [d2133, d4529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16233 (p : Pattern) (guard : d4475 p = 1) : d2134 p ≤ (2 : Int) + d4587 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d2134, d4587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16223 p hg
    simpa only [d2134, d4587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d2134, d4587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16232 p hg
    simpa only [d2134, d4587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16234 (p : Pattern) (guard : d0 p = 1) : d108 p ≤ (2 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare16235 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (2 : Int) + d9 p := by
  change (5 : Int) ≤ (2 : Int) + 9
  decide
theorem compare16236 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (2 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16235 p hg
    simpa only [d106, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d106, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16237 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (2 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16235 p hg
    simpa only [d107, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16236 p hg
    simpa only [d107, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16238 (p : Pattern) (guard : d1 p = 1) : d1960 p ≤ (2 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16235 p hg
    simpa only [d1960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4706 p hg
    simpa only [d1960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16239 (p : Pattern) (guard : d1 p = 1) : d1961 p ≤ (2 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1961, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16238 p hg
    simpa only [d1961, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1961, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4707 p hg
    simpa only [d1961, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
