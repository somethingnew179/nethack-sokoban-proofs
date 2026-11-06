/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons094
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare13300 (p : Pattern) (guard : d4206 p = 1) : d1544 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13249 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12093 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13301 (p : Pattern) (guard : d4206 p = 1) : d1545 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1545, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13300 p hg
    simpa only [d1545, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1545, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12096 p hg
    simpa only [d1545, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13302 (p : Pattern) (guard : d4206 p = 1) : d1546 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1546, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13301 p hg
    simpa only [d1546, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1546, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12103 p hg
    simpa only [d1546, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13303 (p : Pattern) (guard : d4206 p = 1) : d1547 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1547, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13302 p hg
    simpa only [d1547, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1547, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13264 p hg
    simpa only [d1547, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13304 (p : Pattern) (guard : d4206 p = 1) : d1520 p ≤ (2 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12120 p hg
    simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13276 p hg
    simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13305 (p : Pattern) (guard : d4206 p = 1) : d1548 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1548, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13303 p hg
    simpa only [d1548, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1548, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13304 p hg
    simpa only [d1548, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13306 (p : Pattern) (guard : d4206 p = 1) : d1549 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1549, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13305 p hg
    simpa only [d1549, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1549, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13283 p hg
    simpa only [d1549, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13307 (p : Pattern) (guard : d4206 p = 1) : d1550 p ≤ (2 : Int) + d99 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1550, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13283 p hg
    simpa only [d1550, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1550, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1550, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13308 (p : Pattern) (guard : d4206 p = 1) : d1551 p ≤ (2 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1551, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13306 p hg
    simpa only [d1551, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1551, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13307 p hg
    simpa only [d1551, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13309 (p : Pattern) (guard : d4206 p = 1) : d1552 p ≤ (2 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1552, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13299 p hg
    simpa only [d1552, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1552, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13308 p hg
    simpa only [d1552, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13310 (p : Pattern) (guard : d0 p = 1) : d353 p ≤ (2 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13311 (p : Pattern) (guard : d4206 p = 1) : d1553 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1553, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d4206, d1553, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1553, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13310 p hg
    simpa only [d4206, d1553, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13312 (p : Pattern) (guard : d4206 p = 1) : d1554 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13311 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13252 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13313 (p : Pattern) (guard : d4206 p = 1) : d1555 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1555, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13312 p hg
    simpa only [d1555, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1555, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12096 p hg
    simpa only [d1555, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13314 (p : Pattern) (guard : d4206 p = 1) : d1556 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1556, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13313 p hg
    simpa only [d1556, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1556, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12103 p hg
    simpa only [d1556, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13315 (p : Pattern) (guard : d4206 p = 1) : d1557 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1557, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13314 p hg
    simpa only [d1557, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1557, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13264 p hg
    simpa only [d1557, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13316 (p : Pattern) (guard : d4206 p = 1) : d1558 p ≤ (2 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1558, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13249 p hg
    simpa only [d1558, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1558, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12108 p hg
    simpa only [d1558, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13317 (p : Pattern) (guard : d4206 p = 1) : d1559 p ≤ (2 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1559, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13316 p hg
    simpa only [d1559, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1559, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12110 p hg
    simpa only [d1559, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13318 (p : Pattern) (guard : d4206 p = 1) : d1560 p ≤ (2 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1560, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13317 p hg
    simpa only [d1560, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1560, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12119 p hg
    simpa only [d1560, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13319 (p : Pattern) (guard : d4206 p = 1) : d1561 p ≤ (2 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1561, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13318 p hg
    simpa only [d1561, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1561, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13276 p hg
    simpa only [d1561, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13320 (p : Pattern) (guard : d4206 p = 1) : d1562 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1562, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13315 p hg
    simpa only [d1562, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1562, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13319 p hg
    simpa only [d1562, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13321 (p : Pattern) (guard : d4206 p = 1) : d1563 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1563, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13320 p hg
    simpa only [d1563, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1563, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13283 p hg
    simpa only [d1563, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13322 (p : Pattern) (guard : d4206 p = 1) : d1564 p ≤ (2 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1564, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13283 p hg
    simpa only [d1564, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1564, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13297 p hg
    simpa only [d1564, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13323 (p : Pattern) (guard : d4206 p = 1) : d1565 p ≤ (2 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1565, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13321 p hg
    simpa only [d1565, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1565, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13322 p hg
    simpa only [d1565, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13324 (p : Pattern) (guard : d4206 p = 1) : d1566 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1566, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13287 p hg
    simpa only [d1566, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1566, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13264 p hg
    simpa only [d1566, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13325 (p : Pattern) (guard : d4206 p = 1) : d1567 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1567, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13324 p hg
    simpa only [d1567, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1567, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13304 p hg
    simpa only [d1567, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13326 (p : Pattern) (guard : d4206 p = 1) : d1568 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1568, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13325 p hg
    simpa only [d1568, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1568, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13283 p hg
    simpa only [d1568, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13327 (p : Pattern) (guard : d4206 p = 1) : d1569 p ≤ (2 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1569, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13326 p hg
    simpa only [d1569, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1569, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13307 p hg
    simpa only [d1569, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13328 (p : Pattern) (guard : d4206 p = 1) : d1570 p ≤ (2 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1570, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13323 p hg
    simpa only [d1570, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1570, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13327 p hg
    simpa only [d1570, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13329 (p : Pattern) (guard : d4206 p = 1) : d1571 p ≤ (2 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13309 p hg
    simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13328 p hg
    simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13330 (p : Pattern) (guard : d0 p = 1) : d353 p ≤ (2 : Int) + d104 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13331 (p : Pattern) (guard : d4206 p = 1) : d1572 p ≤ (2 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1572, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d4206, d1572, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1572, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13330 p hg
    simpa only [d4206, d1572, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13332 (p : Pattern) (guard : d0 p = 1) : d343 p ≤ (2 : Int) + d104 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13333 (p : Pattern) (guard : d4206 p = 1) : d1573 p ≤ (2 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1573, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d4206, d1573, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1573, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13332 p hg
    simpa only [d4206, d1573, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13334 (p : Pattern) (guard : d4206 p = 1) : d1574 p ≤ (2 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13331 p hg
    simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13333 p hg
    simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13335 (p : Pattern) (guard : d4206 p = 1) : d1575 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1575, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13334 p hg
    simpa only [d1575, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1575, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12194 p hg
    simpa only [d1575, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13336 (p : Pattern) (guard : d4206 p = 1) : d1576 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1576, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13335 p hg
    simpa only [d1576, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1576, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12197 p hg
    simpa only [d1576, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13337 (p : Pattern) (guard : d4206 p = 1) : d124 p ≤ (2 : Int) + d118 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d124, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d4206, d124, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d124, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12201 p hg
    simpa only [d4206, d124, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13338 (p : Pattern) (guard : d4206 p = 1) : d124 p ≤ (2 : Int) + d122 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d124, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d4206, d124, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d124, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12320 p hg
    simpa only [d4206, d124, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13339 (p : Pattern) (guard : d4206 p = 1) : d124 p ≤ (2 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13337 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13338 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13340 (p : Pattern) (guard : d4206 p = 1) : d126 p ≤ (2 : Int) + d126 p := by
  omega
theorem compare13341 (p : Pattern) (guard : d4206 p = 1) : d1577 p ≤ (2 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1577, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13339 p hg
    simpa only [d1577, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1577, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13340 p hg
    simpa only [d1577, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13342 (p : Pattern) (guard : d4206 p = 1) : d129 p ≤ (2 : Int) + d129 p := by
  omega
theorem compare13343 (p : Pattern) (guard : d4206 p = 1) : d1578 p ≤ (2 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1578, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13341 p hg
    simpa only [d1578, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1578, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13342 p hg
    simpa only [d1578, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13344 (p : Pattern) (guard : d4206 p = 1) : d1579 p ≤ (2 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1579, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13336 p hg
    simpa only [d1579, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1579, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13343 p hg
    simpa only [d1579, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13345 (p : Pattern) (guard : d0 p = 1) : d336 p ≤ (2 : Int) + d104 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13346 (p : Pattern) (guard : d4206 p = 1) : d1580 p ≤ (2 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1580, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d4206, d1580, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1580, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13345 p hg
    simpa only [d4206, d1580, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13347 (p : Pattern) (guard : d4206 p = 1) : d1581 p ≤ (2 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1581, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13346 p hg
    simpa only [d1581, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1581, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12202 p hg
    simpa only [d1581, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13348 (p : Pattern) (guard : d4206 p = 1) : d1582 p ≤ (2 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1582, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13347 p hg
    simpa only [d1582, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1582, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12204 p hg
    simpa only [d1582, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13349 (p : Pattern) (guard : d4206 p = 1) : d1583 p ≤ (2 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1583, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13348 p hg
    simpa only [d1583, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1583, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12207 p hg
    simpa only [d1583, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13350 (p : Pattern) (guard : d4206 p = 1) : d139 p ≤ (2 : Int) + d139 p := by
  omega
theorem compare13351 (p : Pattern) (guard : d4206 p = 1) : d1584 p ≤ (2 : Int) + d140 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1584, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13338 p hg
    simpa only [d1584, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1584, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13350 p hg
    simpa only [d1584, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13352 (p : Pattern) (guard : d4206 p = 1) : d141 p ≤ (2 : Int) + d141 p := by
  omega
theorem compare13353 (p : Pattern) (guard : d4206 p = 1) : d1585 p ≤ (2 : Int) + d142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1585, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13351 p hg
    simpa only [d1585, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1585, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13352 p hg
    simpa only [d1585, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13354 (p : Pattern) (guard : d4206 p = 1) : d144 p ≤ (2 : Int) + d144 p := by
  omega
theorem compare13355 (p : Pattern) (guard : d4206 p = 1) : d1586 p ≤ (2 : Int) + d145 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1586, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13353 p hg
    simpa only [d1586, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1586, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13354 p hg
    simpa only [d1586, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13356 (p : Pattern) (guard : d4206 p = 1) : d1587 p ≤ (2 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1587, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13349 p hg
    simpa only [d1587, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1587, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13355 p hg
    simpa only [d1587, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13357 (p : Pattern) (guard : d4206 p = 1) : d1588 p ≤ (2 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1588, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13344 p hg
    simpa only [d1588, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1588, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13356 p hg
    simpa only [d1588, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13358 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (2 : Int) + d120 p := by
  omega
theorem compare13359 (p : Pattern) (guard : d4206 p = 1) : d229 p ≤ (2 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d229, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13358 p hg
    simpa only [d4206, d229, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d229, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12320 p hg
    simpa only [d4206, d229, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13360 (p : Pattern) (guard : d4206 p = 1) : d1053 p ≤ (2 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1053, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12202 p hg
    simpa only [d1053, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1053, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13359 p hg
    simpa only [d1053, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13361 (p : Pattern) (guard : d4206 p = 1) : d1054 p ≤ (2 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1054, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13360 p hg
    simpa only [d1054, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1054, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1054, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13362 (p : Pattern) (guard : d4206 p = 1) : d1589 p ≤ (2 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1589, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13361 p hg
    simpa only [d1589, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1589, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1589, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13363 (p : Pattern) (guard : d4206 p = 1) : d1590 p ≤ (2 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1590, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12198 p hg
    simpa only [d1590, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1590, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13362 p hg
    simpa only [d1590, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13364 (p : Pattern) (guard : d4206 p = 1) : d230 p ≤ (2 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d230, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13359 p hg
    simpa only [d230, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d230, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d230, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13365 (p : Pattern) (guard : d4206 p = 1) : d231 p ≤ (2 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d231, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13364 p hg
    simpa only [d231, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d231, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d231, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13366 (p : Pattern) (guard : d4206 p = 1) : d1591 p ≤ (2 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1591, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13365 p hg
    simpa only [d1591, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1591, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1591, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13367 (p : Pattern) (guard : d4206 p = 1) : d1592 p ≤ (2 : Int) + d156 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1592, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12208 p hg
    simpa only [d1592, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1592, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13366 p hg
    simpa only [d1592, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13368 (p : Pattern) (guard : d4206 p = 1) : d1593 p ≤ (2 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1593, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13363 p hg
    simpa only [d1593, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1593, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13367 p hg
    simpa only [d1593, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13369 (p : Pattern) (guard : d4206 p = 1) : d1594 p ≤ (2 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1594, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13357 p hg
    simpa only [d1594, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1594, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13368 p hg
    simpa only [d1594, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13370 (p : Pattern) (guard : d4206 p = 1) : d1595 p ≤ (2 : Int) + d159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1595, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12196 p hg
    simpa only [d1595, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1595, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1595, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13371 (p : Pattern) (guard : d4206 p = 1) : d1596 p ≤ (2 : Int) + d160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1596, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13370 p hg
    simpa only [d1596, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1596, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1596, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13372 (p : Pattern) (guard : d4206 p = 1) : d1597 p ≤ (2 : Int) + d161 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1597, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13371 p hg
    simpa only [d1597, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1597, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1597, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13373 (p : Pattern) (guard : d4206 p = 1) : d1598 p ≤ (2 : Int) + d162 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1598, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13372 p hg
    simpa only [d1598, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1598, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1598, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13374 (p : Pattern) (guard : d4206 p = 1) : d1599 p ≤ (2 : Int) + d163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1599, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13368 p hg
    simpa only [d1599, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1599, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13373 p hg
    simpa only [d1599, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13375 (p : Pattern) (guard : d4206 p = 1) : d1600 p ≤ (2 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1600, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13369 p hg
    simpa only [d1600, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1600, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13374 p hg
    simpa only [d1600, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13376 (p : Pattern) (guard : d4206 p = 1) : d1601 p ≤ (2 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13333 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12191 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13377 (p : Pattern) (guard : d4206 p = 1) : d1602 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1602, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13376 p hg
    simpa only [d1602, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1602, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12194 p hg
    simpa only [d1602, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13378 (p : Pattern) (guard : d4206 p = 1) : d1603 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1603, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13377 p hg
    simpa only [d1603, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1603, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12197 p hg
    simpa only [d1603, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13379 (p : Pattern) (guard : d4206 p = 1) : d1604 p ≤ (2 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1604, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13378 p hg
    simpa only [d1604, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1604, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13343 p hg
    simpa only [d1604, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13380 (p : Pattern) (guard : d4206 p = 1) : d1586 p ≤ (2 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12208 p hg
    simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13355 p hg
    simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13381 (p : Pattern) (guard : d4206 p = 1) : d1605 p ≤ (2 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1605, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13379 p hg
    simpa only [d1605, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1605, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13380 p hg
    simpa only [d1605, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13382 (p : Pattern) (guard : d4206 p = 1) : d1606 p ≤ (2 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1606, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13381 p hg
    simpa only [d1606, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1606, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13368 p hg
    simpa only [d1606, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13383 (p : Pattern) (guard : d4206 p = 1) : d1607 p ≤ (2 : Int) + d165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1607, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13368 p hg
    simpa only [d1607, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1607, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1607, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13384 (p : Pattern) (guard : d4206 p = 1) : d1608 p ≤ (2 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1608, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13382 p hg
    simpa only [d1608, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1608, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13383 p hg
    simpa only [d1608, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13385 (p : Pattern) (guard : d4206 p = 1) : d1609 p ≤ (2 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1609, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13375 p hg
    simpa only [d1609, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1609, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13384 p hg
    simpa only [d1609, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13386 (p : Pattern) (guard : d4206 p = 1) : d1610 p ≤ (2 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1610, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13309 p hg
    simpa only [d1610, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1610, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13385 p hg
    simpa only [d1610, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13387 (p : Pattern) (guard : d4206 p = 1) : d1611 p ≤ (2 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1611, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13329 p hg
    simpa only [d1611, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1611, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13386 p hg
    simpa only [d1611, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13388 (p : Pattern) (guard : d4206 p = 1) : d66 p ≤ (2 : Int) + d170 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d66, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d4206, d66, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d66, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12253 p hg
    simpa only [d4206, d66, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13389 (p : Pattern) (guard : d4206 p = 1) : d66 p ≤ (2 : Int) + d171 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12108 p hg
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13388 p hg
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13390 (p : Pattern) (guard : d4206 p = 1) : d66 p ≤ (2 : Int) + d172 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d66, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d4206, d66, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d66, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12116 p hg
    simpa only [d4206, d66, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13391 (p : Pattern) (guard : d4206 p = 1) : d173 p ≤ (2 : Int) + d173 p := by
  omega
theorem compare13392 (p : Pattern) (guard : d4206 p = 1) : d176 p ≤ (2 : Int) + d174 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d176, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13390 p hg
    simpa only [d176, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d176, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13391 p hg
    simpa only [d176, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13393 (p : Pattern) (guard : d4206 p = 1) : d1612 p ≤ (2 : Int) + d175 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1612, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13389 p hg
    simpa only [d1612, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1612, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13392 p hg
    simpa only [d1612, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13394 (p : Pattern) (guard : d4206 p = 1) : d177 p ≤ (2 : Int) + d177 p := by
  omega
theorem compare13395 (p : Pattern) (guard : d4206 p = 1) : d1613 p ≤ (2 : Int) + d178 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1613, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13393 p hg
    simpa only [d1613, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1613, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13394 p hg
    simpa only [d1613, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13396 (p : Pattern) (guard : d4206 p = 1) : d1614 p ≤ (2 : Int) + d179 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1614, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13287 p hg
    simpa only [d1614, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1614, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13395 p hg
    simpa only [d1614, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13397 (p : Pattern) (guard : d4206 p = 1) : d1615 p ≤ (2 : Int) + d180 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1615, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13388 p hg
    simpa only [d1615, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1615, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13260 p hg
    simpa only [d1615, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13398 (p : Pattern) (guard : d4206 p = 1) : d181 p ≤ (2 : Int) + d181 p := by
  omega
theorem compare13399 (p : Pattern) (guard : d4206 p = 1) : d1616 p ≤ (2 : Int) + d182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1616, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13397 p hg
    simpa only [d1616, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1616, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13398 p hg
    simpa only [d1616, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13400 (p : Pattern) (guard : d4206 p = 1) : d184 p ≤ (2 : Int) + d184 p := by
  omega
theorem compare13401 (p : Pattern) (guard : d4206 p = 1) : d1617 p ≤ (2 : Int) + d185 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1617, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13399 p hg
    simpa only [d1617, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1617, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13400 p hg
    simpa only [d1617, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13402 (p : Pattern) (guard : d4206 p = 1) : d1618 p ≤ (2 : Int) + d186 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1618, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12120 p hg
    simpa only [d1618, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1618, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13401 p hg
    simpa only [d1618, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13403 (p : Pattern) (guard : d4206 p = 1) : d1619 p ≤ (2 : Int) + d187 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1619, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13396 p hg
    simpa only [d1619, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1619, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13402 p hg
    simpa only [d1619, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13404 (p : Pattern) (guard : d4206 p = 1) : d1620 p ≤ (2 : Int) + d188 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1620, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12093 p hg
    simpa only [d1620, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1620, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12255 p hg
    simpa only [d1620, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13405 (p : Pattern) (guard : d4206 p = 1) : d1621 p ≤ (2 : Int) + d189 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1621, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13404 p hg
    simpa only [d1621, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1621, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12257 p hg
    simpa only [d1621, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13406 (p : Pattern) (guard : d1 p = 1) : d191 p ≤ (2 : Int) + d191 p := by
  omega
theorem compare13407 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d192 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13408 (p : Pattern) (guard : d4206 p = 1) : d1622 p ≤ (2 : Int) + d193 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1622, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13406 p hg
    simpa only [d4206, d1622, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1622, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13407 p hg
    simpa only [d4206, d1622, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13409 (p : Pattern) (guard : d4206 p = 1) : d1623 p ≤ (2 : Int) + d194 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1623, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12095 p hg
    simpa only [d1623, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1623, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13408 p hg
    simpa only [d1623, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13410 (p : Pattern) (guard : d4206 p = 1) : d1624 p ≤ (2 : Int) + d195 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1624, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13409 p hg
    simpa only [d1624, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1624, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1624, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13411 (p : Pattern) (guard : d4206 p = 1) : d1625 p ≤ (2 : Int) + d196 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1625, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13410 p hg
    simpa only [d1625, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1625, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1625, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13412 (p : Pattern) (guard : d4206 p = 1) : d1626 p ≤ (2 : Int) + d197 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1626, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13405 p hg
    simpa only [d1626, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1626, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13411 p hg
    simpa only [d1626, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13413 (p : Pattern) (guard : d4206 p = 1) : d1627 p ≤ (2 : Int) + d198 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1627, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12095 p hg
    simpa only [d1627, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1627, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12117 p hg
    simpa only [d1627, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13414 (p : Pattern) (guard : d4206 p = 1) : d1628 p ≤ (2 : Int) + d199 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1628, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12108 p hg
    simpa only [d1628, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1628, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13413 p hg
    simpa only [d1628, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13415 (p : Pattern) (guard : d4206 p = 1) : d1629 p ≤ (2 : Int) + d200 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1629, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13414 p hg
    simpa only [d1629, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1629, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12267 p hg
    simpa only [d1629, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13416 (p : Pattern) (guard : d4206 p = 1) : d1630 p ≤ (2 : Int) + d201 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1630, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13408 p hg
    simpa only [d1630, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1630, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1630, d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13417 (p : Pattern) (guard : d4206 p = 1) : d1631 p ≤ (2 : Int) + d202 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1631, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13416 p hg
    simpa only [d1631, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1631, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1631, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13418 (p : Pattern) (guard : d4206 p = 1) : d1632 p ≤ (2 : Int) + d203 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1632, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13417 p hg
    simpa only [d1632, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1632, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1632, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13419 (p : Pattern) (guard : d4206 p = 1) : d1633 p ≤ (2 : Int) + d204 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1633, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13415 p hg
    simpa only [d1633, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1633, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13418 p hg
    simpa only [d1633, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13420 (p : Pattern) (guard : d4206 p = 1) : d1634 p ≤ (2 : Int) + d205 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1634, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13412 p hg
    simpa only [d1634, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1634, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13419 p hg
    simpa only [d1634, d205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13421 (p : Pattern) (guard : d4206 p = 1) : d1635 p ≤ (2 : Int) + d206 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1635, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13403 p hg
    simpa only [d1635, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1635, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13420 p hg
    simpa only [d1635, d206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13422 (p : Pattern) (guard : d4206 p = 1) : d1636 p ≤ (2 : Int) + d207 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1636, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13420 p hg
    simpa only [d1636, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1636, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d1636, d207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13423 (p : Pattern) (guard : d4206 p = 1) : d1637 p ≤ (2 : Int) + d208 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1637, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13421 p hg
    simpa only [d1637, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1637, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13422 p hg
    simpa only [d1637, d208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13424 (p : Pattern) (guard : d4206 p = 1) : d1638 p ≤ (2 : Int) + d209 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1638, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13323 p hg
    simpa only [d1638, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1638, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13423 p hg
    simpa only [d1638, d209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13425 (p : Pattern) (guard : d4206 p = 1) : d1639 p ≤ (2 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1639, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13309 p hg
    simpa only [d1639, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1639, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13424 p hg
    simpa only [d1639, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13426 (p : Pattern) (guard : d4206 p = 1) : d1640 p ≤ (2 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1640, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13347 p hg
    simpa only [d1640, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1640, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12294 p hg
    simpa only [d1640, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13427 (p : Pattern) (guard : d4206 p = 1) : d1641 p ≤ (2 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1641, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13426 p hg
    simpa only [d1641, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1641, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12296 p hg
    simpa only [d1641, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13428 (p : Pattern) (guard : d4206 p = 1) : d215 p ≤ (2 : Int) + d215 p := by
  omega
theorem compare13429 (p : Pattern) (guard : d4206 p = 1) : d1642 p ≤ (2 : Int) + d216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1642, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13351 p hg
    simpa only [d1642, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1642, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13428 p hg
    simpa only [d1642, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13430 (p : Pattern) (guard : d4206 p = 1) : d217 p ≤ (2 : Int) + d217 p := by
  omega
theorem compare13431 (p : Pattern) (guard : d4206 p = 1) : d1643 p ≤ (2 : Int) + d218 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1643, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13429 p hg
    simpa only [d1643, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1643, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13430 p hg
    simpa only [d1643, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13432 (p : Pattern) (guard : d4206 p = 1) : d1644 p ≤ (2 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1644, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13427 p hg
    simpa only [d1644, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1644, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13431 p hg
    simpa only [d1644, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13433 (p : Pattern) (guard : d4206 p = 1) : d1645 p ≤ (2 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1645, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13344 p hg
    simpa only [d1645, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1645, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13432 p hg
    simpa only [d1645, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13434 (p : Pattern) (guard : d4206 p = 1) : d1646 p ≤ (2 : Int) + d221 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1646, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12297 p hg
    simpa only [d1646, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1646, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13366 p hg
    simpa only [d1646, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13435 (p : Pattern) (guard : d4206 p = 1) : d1647 p ≤ (2 : Int) + d222 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1647, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13363 p hg
    simpa only [d1647, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1647, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13434 p hg
    simpa only [d1647, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13436 (p : Pattern) (guard : d4206 p = 1) : d1648 p ≤ (2 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1648, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13433 p hg
    simpa only [d1648, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1648, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13435 p hg
    simpa only [d1648, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13437 (p : Pattern) (guard : d4206 p = 1) : d1649 p ≤ (2 : Int) + d224 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1649, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13435 p hg
    simpa only [d1649, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1649, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13373 p hg
    simpa only [d1649, d224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13438 (p : Pattern) (guard : d4206 p = 1) : d1650 p ≤ (2 : Int) + d225 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1650, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13436 p hg
    simpa only [d1650, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1650, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13437 p hg
    simpa only [d1650, d225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13439 (p : Pattern) (guard : d4206 p = 1) : d139 p ≤ (2 : Int) + d226 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d139, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2186 p hg
    simpa only [d4206, d139, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d139, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12320 p hg
    simpa only [d4206, d139, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
