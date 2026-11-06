import NetHack.Soko22Hazard87.Compare027
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7000 (p : Pattern) (guard : d1569 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6969 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1568 p = 1 := by simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6999 p hg
    simpa only [d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7001 (p : Pattern) (guard : d1570 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1569 p = 1 := by simpa only [d1570, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7000 p hg
    simpa only [d1570, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1570, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1570, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7002 (p : Pattern) (guard : d1571 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1570 p = 1 := by simpa only [d1571, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7001 p hg
    simpa only [d1571, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1571, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1571, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7003 (p : Pattern) (guard : d1864 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1863 p = 1 := by simpa only [d1864, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6989 p hg
    simpa only [d1864, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1864, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7002 p hg
    simpa only [d1864, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7004 (p : Pattern) (guard : d1865 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1864 p = 1 := by simpa only [d1865, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7003 p hg
    simpa only [d1865, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1865, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d1865, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7005 (p : Pattern) (guard : d1866 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1860 p = 1 := by simpa only [d1866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6974 p hg
    simpa only [d1866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1865 p = 1 := by simpa only [d1866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7004 p hg
    simpa only [d1866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7006 (p : Pattern) (guard : d1867 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1861 p = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6975 p hg
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1866 p = 1 := by simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7005 p hg
    simpa only [d1867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7007 (p : Pattern) (guard : d1575 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6976 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7008 (p : Pattern) (guard : d1576 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1575 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7007 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6284 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7009 (p : Pattern) (guard : d1577 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7008 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6982 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7010 (p : Pattern) (guard : d1578 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1565 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6982 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7011 (p : Pattern) (guard : d1579 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1577 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7009 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7010 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7012 (p : Pattern) (guard : d1580 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1579 p = 1 := by simpa only [d1580, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7011 p hg
    simpa only [d1580, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1580, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d1580, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7013 (p : Pattern) (guard : d1581 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6985 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1580 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7012 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7014 (p : Pattern) (guard : d1868 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1868, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d1868, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1581 p = 1 := by simpa only [d1868, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7013 p hg
    simpa only [d1868, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7015 (p : Pattern) (guard : d1582 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6496 p hg
    simpa only [d1582, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d1582, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7016 (p : Pattern) (guard : d1869 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1868 p = 1 := by simpa only [d1869, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7014 p hg
    simpa only [d1869, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1582 p = 1 := by simpa only [d1869, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7015 p hg
    simpa only [d1869, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7017 (p : Pattern) (guard : d1575 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6990 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7018 (p : Pattern) (guard : d1576 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1575 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7017 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6293 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7019 (p : Pattern) (guard : d1577 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7018 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6996 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7020 (p : Pattern) (guard : d1578 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1565 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6996 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7021 (p : Pattern) (guard : d1579 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1577 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7019 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7020 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7022 (p : Pattern) (guard : d1580 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1579 p = 1 := by simpa only [d1580, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7021 p hg
    simpa only [d1580, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1580, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d1580, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7023 (p : Pattern) (guard : d1581 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6999 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1580 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7022 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7024 (p : Pattern) (guard : d1582 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7023 p hg
    simpa only [d1582, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1582, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7025 (p : Pattern) (guard : d1583 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1582 p = 1 := by simpa only [d1583, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7024 p hg
    simpa only [d1583, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1583, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1583, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7026 (p : Pattern) (guard : d1870 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1869 p = 1 := by simpa only [d1870, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7016 p hg
    simpa only [d1870, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1870, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7025 p hg
    simpa only [d1870, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7027 (p : Pattern) (guard : d1871 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1870 p = 1 := by simpa only [d1871, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7026 p hg
    simpa only [d1871, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1871, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d1871, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7028 (p : Pattern) (guard : d1872 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1865 p = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7004 p hg
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1871 p = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7027 p hg
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7029 (p : Pattern) (guard : d1873 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1866 p = 1 := by simpa only [d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7005 p hg
    simpa only [d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1872 p = 1 := by simpa only [d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7028 p hg
    simpa only [d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7030 (p : Pattern) (guard : d1874 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1867 p = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7006 p hg
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1873 p = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7029 p hg
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7031 (p : Pattern) (guard : d1875 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1875, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d1875, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1874 p = 1 := by simpa only [d1875, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7030 p hg
    simpa only [d1875, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7032 (p : Pattern) (guard : d1876 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1876, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d1876, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1875 p = 1 := by simpa only [d1876, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7031 p hg
    simpa only [d1876, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7033 (p : Pattern) (guard : d1877 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1871 p = 1 := by simpa only [d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7027 p hg
    simpa only [d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d1877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7034 (p : Pattern) (guard : d1878 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1872 p = 1 := by simpa only [d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7028 p hg
    simpa only [d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1877 p = 1 := by simpa only [d1878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7033 p hg
    simpa only [d1878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7035 (p : Pattern) (guard : d1879 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1873 p = 1 := by simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7029 p hg
    simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1878 p = 1 := by simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7034 p hg
    simpa only [d1879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7036 (p : Pattern) (guard : d1880 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1880, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d1880, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1879 p = 1 := by simpa only [d1880, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7035 p hg
    simpa only [d1880, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7037 (p : Pattern) (guard : d1881 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1881, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d1881, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1880 p = 1 := by simpa only [d1881, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7036 p hg
    simpa only [d1881, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7038 (p : Pattern) (guard : d1882 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1876 p = 1 := by simpa only [d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7032 p hg
    simpa only [d1882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1881 p = 1 := by simpa only [d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7037 p hg
    simpa only [d1882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7039 (p : Pattern) (guard : d1593 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7008 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7040 (p : Pattern) (guard : d1594 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1593 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7039 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7041 (p : Pattern) (guard : d1595 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1594 p = 1 := by simpa only [d1595, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7040 p hg
    simpa only [d1595, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1595, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d1595, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7042 (p : Pattern) (guard : d1596 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1595 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7041 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4533 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7043 (p : Pattern) (guard : d1883 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1883, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d1883, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1596 p = 1 := by simpa only [d1883, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7042 p hg
    simpa only [d1883, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7044 (p : Pattern) (guard : d1597 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1596 p = 1 := by simpa only [d1597, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6511 p hg
    simpa only [d1597, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1597, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d1597, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7045 (p : Pattern) (guard : d1884 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1883 p = 1 := by simpa only [d1884, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7043 p hg
    simpa only [d1884, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1597 p = 1 := by simpa only [d1884, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7044 p hg
    simpa only [d1884, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7046 (p : Pattern) (guard : d1593 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7018 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7047 (p : Pattern) (guard : d1594 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1593 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7046 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7048 (p : Pattern) (guard : d1595 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1594 p = 1 := by simpa only [d1595, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7047 p hg
    simpa only [d1595, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1595, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d1595, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7049 (p : Pattern) (guard : d1596 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1595 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7048 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4551 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7050 (p : Pattern) (guard : d1597 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1596 p = 1 := by simpa only [d1597, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7049 p hg
    simpa only [d1597, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1597, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1597, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7051 (p : Pattern) (guard : d1598 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1597 p = 1 := by simpa only [d1598, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7050 p hg
    simpa only [d1598, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1598, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d1598, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7052 (p : Pattern) (guard : d1885 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1884 p = 1 := by simpa only [d1885, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7045 p hg
    simpa only [d1885, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1598 p = 1 := by simpa only [d1885, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7051 p hg
    simpa only [d1885, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7053 (p : Pattern) (guard : d1886 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1885 p = 1 := by simpa only [d1886, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7052 p hg
    simpa only [d1886, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1886, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d1886, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7054 (p : Pattern) (guard : d1887 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1886 p = 1 := by simpa only [d1887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7053 p hg
    simpa only [d1887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d1887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7055 (p : Pattern) (guard : d1888 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1877 p = 1 := by simpa only [d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7033 p hg
    simpa only [d1888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1887 p = 1 := by simpa only [d1888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7054 p hg
    simpa only [d1888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7056 (p : Pattern) (guard : d1889 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1878 p = 1 := by simpa only [d1889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7034 p hg
    simpa only [d1889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1888 p = 1 := by simpa only [d1889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7055 p hg
    simpa only [d1889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7057 (p : Pattern) (guard : d1890 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1890, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d1890, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1889 p = 1 := by simpa only [d1890, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7056 p hg
    simpa only [d1890, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7058 (p : Pattern) (guard : d1891 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1891, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d1891, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1890 p = 1 := by simpa only [d1891, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7057 p hg
    simpa only [d1891, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7059 (p : Pattern) (guard : d1892 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1881 p = 1 := by simpa only [d1892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7037 p hg
    simpa only [d1892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1891 p = 1 := by simpa only [d1892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7058 p hg
    simpa only [d1892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7060 (p : Pattern) (guard : d1893 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1882 p = 1 := by simpa only [d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7038 p hg
    simpa only [d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1892 p = 1 := by simpa only [d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7059 p hg
    simpa only [d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7061 (p : Pattern) (guard : d1894 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1893 p = 1 := by simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7060 p hg
    simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7062 (p : Pattern) (guard : d1895 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1894 p = 1 := by simpa only [d1895, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7061 p hg
    simpa only [d1895, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1895, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d1895, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7063 (p : Pattern) (guard : d1896 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1896, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d1896, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1895 p = 1 := by simpa only [d1896, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7062 p hg
    simpa only [d1896, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7064 (p : Pattern) (guard : d7080 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1881 p = 1 := by simpa only [d7080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7037 p hg
    simpa only [d7080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d7080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7065 (p : Pattern) (guard : d6495 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1872 p = 1 := by simpa only [d6495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7028 p hg
    simpa only [d6495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d6495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7066 (p : Pattern) (guard : d5121 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d825 p = 1 := by simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5669 p hg
    simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7067 (p : Pattern) (guard : d5122 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5121 p = 1 := by simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7066 p hg
    simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6944 p hg
    simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7068 (p : Pattern) (guard : d5123 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5122 p = 1 := by simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7067 p hg
    simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1563 p = 1 := by simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6980 p hg
    simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7069 (p : Pattern) (guard : d5124 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5123 p = 1 := by simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7068 p hg
    simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7070 (p : Pattern) (guard : d5125 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6942 p hg
    simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5124 p = 1 := by simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7069 p hg
    simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7071 (p : Pattern) (guard : d5126 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5125 p = 1 := by simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7070 p hg
    simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6983 p hg
    simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7072 (p : Pattern) (guard : d5127 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5126 p = 1 := by simpa only [d5127, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7071 p hg
    simpa only [d5127, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5127, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d5127, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7073 (p : Pattern) (guard : d5128 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1563 p = 1 := by simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6980 p hg
    simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7074 (p : Pattern) (guard : d5129 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5128 p = 1 := by simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7073 p hg
    simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7075 (p : Pattern) (guard : d5130 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d5129 p = 1 := by simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7074 p hg
    simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6982 p hg
    simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7076 (p : Pattern) (guard : d5131 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5130 p = 1 := by simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7075 p hg
    simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7010 p hg
    simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7077 (p : Pattern) (guard : d5132 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5131 p = 1 := by simpa only [d5132, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7076 p hg
    simpa only [d5132, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5132, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d5132, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7078 (p : Pattern) (guard : d5133 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5127 p = 1 := by simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7072 p hg
    simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5132 p = 1 := by simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7077 p hg
    simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7079 (p : Pattern) (guard : d6496 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6496, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d6496, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5133 p = 1 := by simpa only [d6496, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7078 p hg
    simpa only [d6496, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7080 (p : Pattern) (guard : d5134 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5133 p = 1 := by simpa only [d5134, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6608 p hg
    simpa only [d5134, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5134, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d5134, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7081 (p : Pattern) (guard : d6497 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6496 p = 1 := by simpa only [d6497, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7079 p hg
    simpa only [d6497, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5134 p = 1 := by simpa only [d6497, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7080 p hg
    simpa only [d6497, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7082 (p : Pattern) (guard : d5121 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d825 p = 1 := by simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5686 p hg
    simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d5121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7083 (p : Pattern) (guard : d5122 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5121 p = 1 := by simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7082 p hg
    simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6963 p hg
    simpa only [d5122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7084 (p : Pattern) (guard : d5123 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5122 p = 1 := by simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7083 p hg
    simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1563 p = 1 := by simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6994 p hg
    simpa only [d5123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7085 (p : Pattern) (guard : d5124 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5123 p = 1 := by simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7084 p hg
    simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d5124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7086 (p : Pattern) (guard : d5125 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6961 p hg
    simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5124 p = 1 := by simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7085 p hg
    simpa only [d5125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7087 (p : Pattern) (guard : d5126 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5125 p = 1 := by simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7086 p hg
    simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1566 p = 1 := by simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6997 p hg
    simpa only [d5126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7088 (p : Pattern) (guard : d5127 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5126 p = 1 := by simpa only [d5127, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7087 p hg
    simpa only [d5127, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5127, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d5127, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7089 (p : Pattern) (guard : d5128 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1563 p = 1 := by simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6994 p hg
    simpa only [d5128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7090 (p : Pattern) (guard : d5129 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5128 p = 1 := by simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7089 p hg
    simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d5129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7091 (p : Pattern) (guard : d5130 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d5129 p = 1 := by simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7090 p hg
    simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6996 p hg
    simpa only [d5130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7092 (p : Pattern) (guard : d5131 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5130 p = 1 := by simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7091 p hg
    simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7020 p hg
    simpa only [d5131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7093 (p : Pattern) (guard : d5132 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5131 p = 1 := by simpa only [d5132, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7092 p hg
    simpa only [d5132, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5132, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d5132, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7094 (p : Pattern) (guard : d5133 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5127 p = 1 := by simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7088 p hg
    simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5132 p = 1 := by simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7093 p hg
    simpa only [d5133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7095 (p : Pattern) (guard : d5134 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5133 p = 1 := by simpa only [d5134, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7094 p hg
    simpa only [d5134, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5134, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d5134, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7096 (p : Pattern) (guard : d5135 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5134 p = 1 := by simpa only [d5135, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7095 p hg
    simpa only [d5135, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5135, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d5135, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7097 (p : Pattern) (guard : d6498 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d6497 p = 1 := by simpa only [d6498, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7081 p hg
    simpa only [d6498, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5135 p = 1 := by simpa only [d6498, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7096 p hg
    simpa only [d6498, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7098 (p : Pattern) (guard : d6499 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6498 p = 1 := by simpa only [d6499, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7097 p hg
    simpa only [d6499, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6499, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d6499, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7099 (p : Pattern) (guard : d6500 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d6499 p = 1 := by simpa only [d6500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7098 p hg
    simpa only [d6500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d6500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7100 (p : Pattern) (guard : d6501 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d6500 p = 1 := by simpa only [d6501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7099 p hg
    simpa only [d6501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d6501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7101 (p : Pattern) (guard : d6502 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d6495 p = 1 := by simpa only [d6502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7065 p hg
    simpa only [d6502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6501 p = 1 := by simpa only [d6502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7100 p hg
    simpa only [d6502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7102 (p : Pattern) (guard : d6503 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6503, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d6503, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6502 p = 1 := by simpa only [d6503, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7101 p hg
    simpa only [d6503, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7103 (p : Pattern) (guard : d6504 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6504, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d6504, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6503 p = 1 := by simpa only [d6504, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7102 p hg
    simpa only [d6504, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7104 (p : Pattern) (guard : d6505 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d6504 p = 1 := by simpa only [d6505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7103 p hg
    simpa only [d6505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d6505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7105 (p : Pattern) (guard : d7081 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d7080 p = 1 := by simpa only [d7081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7064 p hg
    simpa only [d7081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6505 p = 1 := by simpa only [d7081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7104 p hg
    simpa only [d7081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7106 (p : Pattern) (guard : d7082 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d7081 p = 1 := by simpa only [d7082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7105 p hg
    simpa only [d7082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d7082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7107 (p : Pattern) (guard : d7083 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d7082 p = 1 := by simpa only [d7083, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7106 p hg
    simpa only [d7083, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7083, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d7083, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7108 (p : Pattern) (guard : d7084 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d7084, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d7084, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7083 p = 1 := by simpa only [d7084, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7107 p hg
    simpa only [d7084, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7109 (p : Pattern) (guard : d7085 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1896 p = 1 := by simpa only [d7085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7063 p hg
    simpa only [d7085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7084 p = 1 := by simpa only [d7085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7108 p hg
    simpa only [d7085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7110 (p : Pattern) (guard : d7086 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d7085 p = 1 := by simpa only [d7086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d7086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d7086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7111 (p : Pattern) (guard : d7087 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d7086 p = 1 := by simpa only [d7087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7110 p hg
    simpa only [d7087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d7087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7112 (p : Pattern) (guard : d7088 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d7087 p = 1 := by simpa only [d7088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7111 p hg
    simpa only [d7088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d7088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7113 (p : Pattern) (guard : d6506 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1892 p = 1 := by simpa only [d6506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7059 p hg
    simpa only [d6506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6505 p = 1 := by simpa only [d6506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7104 p hg
    simpa only [d6506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7114 (p : Pattern) (guard : d6507 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d6506 p = 1 := by simpa only [d6507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7113 p hg
    simpa only [d6507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d6507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7115 (p : Pattern) (guard : d6508 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6507 p = 1 := by simpa only [d6508, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7114 p hg
    simpa only [d6508, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6508, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d6508, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7116 (p : Pattern) (guard : d6509 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6509, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d6509, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6508 p = 1 := by simpa only [d6509, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7115 p hg
    simpa only [d6509, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7117 (p : Pattern) (guard : d1897 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1891 p = 1 := by simpa only [d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7058 p hg
    simpa only [d1897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d1897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7118 (p : Pattern) (guard : d1906 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1897 p = 1 := by simpa only [d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7117 p hg
    simpa only [d1906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d1906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7119 (p : Pattern) (guard : d1907 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1906 p = 1 := by simpa only [d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7118 p hg
    simpa only [d1907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d1907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7120 (p : Pattern) (guard : d1908 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1907 p = 1 := by simpa only [d1908, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7119 p hg
    simpa only [d1908, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1908, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d1908, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7121 (p : Pattern) (guard : d1909 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1909, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d1909, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1908 p = 1 := by simpa only [d1909, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7120 p hg
    simpa only [d1909, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7122 (p : Pattern) (guard : d7089 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d6509 p = 1 := by simpa only [d7089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7116 p hg
    simpa only [d7089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1909 p = 1 := by simpa only [d7089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7121 p hg
    simpa only [d7089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7123 (p : Pattern) (guard : d7090 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d7089 p = 1 := by simpa only [d7090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7122 p hg
    simpa only [d7090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d7090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7124 (p : Pattern) (guard : d7091 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d7090 p = 1 := by simpa only [d7091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7123 p hg
    simpa only [d7091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d7091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7125 (p : Pattern) (guard : d7092 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d7091 p = 1 := by simpa only [d7092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7124 p hg
    simpa only [d7092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d7092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d7092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7126 (p : Pattern) (guard : d7093 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d7088 p = 1 := by simpa only [d7093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7112 p hg
    simpa only [d7093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d7092 p = 1 := by simpa only [d7093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7125 p hg
    simpa only [d7093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7127 (p : Pattern) (guard : d82212 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d7093 p = 1 := by simpa only [d82212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7126 p hg
    simpa only [d82212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7128 (p : Pattern) (guard : d1898 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1892 p = 1 := by simpa only [d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7059 p hg
    simpa only [d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1897 p = 1 := by simpa only [d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7117 p hg
    simpa only [d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7129 (p : Pattern) (guard : d1899 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1898 p = 1 := by simpa only [d1899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7128 p hg
    simpa only [d1899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d1899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7130 (p : Pattern) (guard : d1900 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1899 p = 1 := by simpa only [d1900, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7129 p hg
    simpa only [d1900, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1900, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d1900, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7131 (p : Pattern) (guard : d1901 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1901, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d1901, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1900 p = 1 := by simpa only [d1901, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7130 p hg
    simpa only [d1901, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7132 (p : Pattern) (guard : d6521 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1901 p = 1 := by simpa only [d6521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7131 p hg
    simpa only [d6521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7133 (p : Pattern) (guard : d6522 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6521 p = 1 := by simpa only [d6522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7132 p hg
    simpa only [d6522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7134 (p : Pattern) (guard : d6523 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6522 p = 1 := by simpa only [d6523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7133 p hg
    simpa only [d6523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7135 (p : Pattern) (guard : d6524 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6523 p = 1 := by simpa only [d6524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7134 p hg
    simpa only [d6524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7136 (p : Pattern) (guard : d6525 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6524 p = 1 := by simpa only [d6525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7135 p hg
    simpa only [d6525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7137 (p : Pattern) (guard : d6526 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6525 p = 1 := by simpa only [d6526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7136 p hg
    simpa only [d6526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7138 (p : Pattern) (guard : d82213 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82212 p = 1 := by simpa only [d82213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7127 p hg
    simpa only [d82213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6526 p = 1 := by simpa only [d82213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7137 p hg
    simpa only [d82213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7139 (p : Pattern) (guard : d82214 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82213 p = 1 := by simpa only [d82214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7138 p hg
    simpa only [d82214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7140 (p : Pattern) (guard : d82215 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82214 p = 1 := by simpa only [d82215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7139 p hg
    simpa only [d82215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7141 (p : Pattern) (guard : d82216 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82216, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82216, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82215 p = 1 := by simpa only [d82216, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7140 p hg
    simpa only [d82216, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7142 (p : Pattern) (guard : d82217 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d82217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82216 p = 1 := by simpa only [d82217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7141 p hg
    simpa only [d82217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7143 (p : Pattern) (guard : d1971 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1909 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7121 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7144 (p : Pattern) (guard : d1972 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1971 p = 1 := by simpa only [d1972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7143 p hg
    simpa only [d1972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7145 (p : Pattern) (guard : d1973 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1972 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7144 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7146 (p : Pattern) (guard : d1974 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1973 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7145 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7147 (p : Pattern) (guard : d1975 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1974 p = 1 := by simpa only [d1975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7146 p hg
    simpa only [d1975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7148 (p : Pattern) (guard : d1976 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1975 p = 1 := by simpa only [d1976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7147 p hg
    simpa only [d1976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7149 (p : Pattern) (guard : d1977 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1976 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7148 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7150 (p : Pattern) (guard : d1978 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1977 p = 1 := by simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7149 p hg
    simpa only [d1978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7151 (p : Pattern) (guard : d1979 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1978 p = 1 := by simpa only [d1979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7150 p hg
    simpa only [d1979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7152 (p : Pattern) (guard : d1980 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1980, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1980, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1979 p = 1 := by simpa only [d1980, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7151 p hg
    simpa only [d1980, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7153 (p : Pattern) (guard : d1981 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1980 p = 1 := by simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7152 p hg
    simpa only [d1981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7154 (p : Pattern) (guard : d82218 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d82217 p = 1 := by simpa only [d82218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7142 p hg
    simpa only [d82218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1981 p = 1 := by simpa only [d82218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7153 p hg
    simpa only [d82218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7155 (p : Pattern) (guard : d82219 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d82218 p = 1 := by simpa only [d82219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7154 p hg
    simpa only [d82219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d82219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7156 (p : Pattern) (guard : d82220 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d82219 p = 1 := by simpa only [d82220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7155 p hg
    simpa only [d82220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d82220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7157 (p : Pattern) (guard : d82221 p = 1) : d47865 p ≤ (-1 : Int) + d98795 p := by
  cases selected : p 49 with
  | false =>
    have hg : d82220 p = 1 := by simpa only [d82221, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7156 p hg
    simpa only [d82221, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82221, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4585 p hg
    simpa only [d82221, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7158 (p : Pattern) (guard : d82222 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 48 with
  | false =>
    have hg : d82211 p = 1 := by simpa only [d82222, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6876 p hg
    simpa only [d82222, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82221 p = 1 := by simpa only [d82222, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7157 p hg
    simpa only [d82222, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7159 (p : Pattern) (guard : d82223 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82222 p = 1 := by simpa only [d82223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7158 p hg
    simpa only [d82223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7160 (p : Pattern) (guard : d82224 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82223 p = 1 := by simpa only [d82224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7159 p hg
    simpa only [d82224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7161 (p : Pattern) (guard : d82225 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82224 p = 1 := by simpa only [d82225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7160 p hg
    simpa only [d82225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7162 (p : Pattern) (guard : d82226 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82225 p = 1 := by simpa only [d82226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7161 p hg
    simpa only [d82226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7163 (p : Pattern) (guard : d82227 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82226 p = 1 := by simpa only [d82227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7162 p hg
    simpa only [d82227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7164 (p : Pattern) (guard : d82228 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82227 p = 1 := by simpa only [d82228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7163 p hg
    simpa only [d82228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7165 (p : Pattern) (guard : d82229 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82228 p = 1 := by simpa only [d82229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7164 p hg
    simpa only [d82229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7166 (p : Pattern) (guard : d82230 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82229 p = 1 := by simpa only [d82230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7165 p hg
    simpa only [d82230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7167 (p : Pattern) (guard : d82231 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82230 p = 1 := by simpa only [d82231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7166 p hg
    simpa only [d82231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7168 (p : Pattern) (guard : d82232 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d82189 p = 1 := by simpa only [d82232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6432 p hg
    simpa only [d82232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82231 p = 1 := by simpa only [d82232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7167 p hg
    simpa only [d82232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7169 (p : Pattern) (guard : d1997 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4811 p hg
    simpa only [d1997, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4406 p hg
    simpa only [d1997, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7170 (p : Pattern) (guard : d1998 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7169 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7171 (p : Pattern) (guard : d1999 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7170 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7172 (p : Pattern) (guard : d2000 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7171 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7173 (p : Pattern) (guard : d2001 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1523 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6438 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7174 (p : Pattern) (guard : d2002 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2001 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7173 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7175 (p : Pattern) (guard : d2003 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2002 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7174 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7176 (p : Pattern) (guard : d2004 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7172 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2003 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7175 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7177 (p : Pattern) (guard : d2005 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6438 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7178 (p : Pattern) (guard : d2006 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7177 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7179 (p : Pattern) (guard : d2007 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7178 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7180 (p : Pattern) (guard : d2008 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2007 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7179 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7181 (p : Pattern) (guard : d2009 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2004 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7176 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2008 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7180 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7182 (p : Pattern) (guard : d2010 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2009 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7181 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7183 (p : Pattern) (guard : d2011 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2010 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7182 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7184 (p : Pattern) (guard : d2012 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2011 p = 1 := by simpa only [d2012, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7183 p hg
    simpa only [d2012, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2012, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d2012, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7185 (p : Pattern) (guard : d2013 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7169 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7186 (p : Pattern) (guard : d2014 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7170 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7185 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7187 (p : Pattern) (guard : d2015 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1999 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7171 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7186 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7188 (p : Pattern) (guard : d2016 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d2016, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4619 p hg
    simpa only [d2016, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2016, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4406 p hg
    simpa only [d2016, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7189 (p : Pattern) (guard : d2017 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7169 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2016 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7188 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7190 (p : Pattern) (guard : d2018 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2017 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7189 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7191 (p : Pattern) (guard : d2019 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7174 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2018 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7190 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7192 (p : Pattern) (guard : d2020 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2015 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7187 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2019 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7191 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7193 (p : Pattern) (guard : d2021 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d2016 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7188 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7194 (p : Pattern) (guard : d2022 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2021 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7193 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7195 (p : Pattern) (guard : d2023 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7178 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2022 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7194 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7196 (p : Pattern) (guard : d2024 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2023 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7195 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7197 (p : Pattern) (guard : d2025 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2020 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7192 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2024 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7196 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7198 (p : Pattern) (guard : d2026 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2009 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7181 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2025 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7197 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7199 (p : Pattern) (guard : d2027 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7185 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7200 (p : Pattern) (guard : d2028 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7199 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7201 (p : Pattern) (guard : d2029 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7200 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7202 (p : Pattern) (guard : d2030 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7201 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7203 (p : Pattern) (guard : d2031 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7202 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7204 (p : Pattern) (guard : d2032 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2026 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7198 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7203 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7205 (p : Pattern) (guard : d2033 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2032 p = 1 := by simpa only [d2033, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7204 p hg
    simpa only [d2033, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2033, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d2033, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7206 (p : Pattern) (guard : d2034 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2012 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7184 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2033 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7205 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7207 (p : Pattern) (guard : d2035 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2034 p = 1 := by simpa only [d2035, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7206 p hg
    simpa only [d2035, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2035, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d2035, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7208 (p : Pattern) (guard : d2036 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2035 p = 1 := by simpa only [d2036, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7207 p hg
    simpa only [d2036, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2036, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d2036, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7209 (p : Pattern) (guard : d2037 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2037, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d2037, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2036 p = 1 := by simpa only [d2037, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7208 p hg
    simpa only [d2037, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7210 (p : Pattern) (guard : d2038 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2037 p = 1 := by simpa only [d2038, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7209 p hg
    simpa only [d2038, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2038, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d2038, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7211 (p : Pattern) (guard : d2039 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7186 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7199 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7212 (p : Pattern) (guard : d2040 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2018 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7190 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7213 (p : Pattern) (guard : d2041 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2039 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7211 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7212 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7214 (p : Pattern) (guard : d2042 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2022 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7194 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7215 (p : Pattern) (guard : d2043 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2042 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7214 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7216 (p : Pattern) (guard : d2044 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2041 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7213 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7215 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7217 (p : Pattern) (guard : d2045 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7197 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2044 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7216 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7218 (p : Pattern) (guard : d2046 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2027 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7199 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7219 (p : Pattern) (guard : d2047 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2046 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7218 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7220 (p : Pattern) (guard : d2048 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2047 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7219 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7221 (p : Pattern) (guard : d2049 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7202 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7220 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7222 (p : Pattern) (guard : d2050 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2045 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7217 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7221 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7223 (p : Pattern) (guard : d2051 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2050 p = 1 := by simpa only [d2051, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7222 p hg
    simpa only [d2051, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2051, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d2051, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7224 (p : Pattern) (guard : d2052 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2033 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7205 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2051 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7223 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7225 (p : Pattern) (guard : d2053 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2052 p = 1 := by simpa only [d2053, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7224 p hg
    simpa only [d2053, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2053, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d2053, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7226 (p : Pattern) (guard : d2054 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2053 p = 1 := by simpa only [d2054, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7225 p hg
    simpa only [d2054, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2054, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d2054, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7227 (p : Pattern) (guard : d2055 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2055, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d2055, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2055, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7226 p hg
    simpa only [d2055, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7228 (p : Pattern) (guard : d2056 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7227 p hg
    simpa only [d2056, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d2056, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7229 (p : Pattern) (guard : d2057 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2038 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7210 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2056 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7228 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7230 (p : Pattern) (guard : d2058 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7212 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7231 (p : Pattern) (guard : d2059 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2058 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7230 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7215 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7232 (p : Pattern) (guard : d2060 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7231 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7220 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7233 (p : Pattern) (guard : d2061 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2048 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7220 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7234 (p : Pattern) (guard : d2062 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2060 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7232 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7233 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7235 (p : Pattern) (guard : d2063 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2062 p = 1 := by simpa only [d2063, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7234 p hg
    simpa only [d2063, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2063, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d2063, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7236 (p : Pattern) (guard : d2064 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2051 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7223 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2063 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7235 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7237 (p : Pattern) (guard : d2065 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2064 p = 1 := by simpa only [d2065, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7236 p hg
    simpa only [d2065, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2065, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d2065, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7238 (p : Pattern) (guard : d2066 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2065 p = 1 := by simpa only [d2066, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7237 p hg
    simpa only [d2066, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2066, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d2066, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7239 (p : Pattern) (guard : d2067 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2067, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d2067, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2067, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7238 p hg
    simpa only [d2067, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7240 (p : Pattern) (guard : d2068 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7239 p hg
    simpa only [d2068, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d2068, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7241 (p : Pattern) (guard : d2069 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2056 p = 1 := by simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7228 p hg
    simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2068 p = 1 := by simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7240 p hg
    simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7242 (p : Pattern) (guard : d2070 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2057 p = 1 := by simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7229 p hg
    simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2069 p = 1 := by simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7241 p hg
    simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7243 (p : Pattern) (guard : d2071 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2068 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7240 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7244 (p : Pattern) (guard : d2072 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2069 p = 1 := by simpa only [d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7241 p hg
    simpa only [d2072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2071 p = 1 := by simpa only [d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7243 p hg
    simpa only [d2072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7245 (p : Pattern) (guard : d2073 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d2070 p = 1 := by simpa only [d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7242 p hg
    simpa only [d2073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2072 p = 1 := by simpa only [d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7244 p hg
    simpa only [d2073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7246 (p : Pattern) (guard : d2074 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2074, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d2074, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2073 p = 1 := by simpa only [d2074, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7245 p hg
    simpa only [d2074, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7247 (p : Pattern) (guard : d2075 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2075, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d2075, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2074 p = 1 := by simpa only [d2075, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7246 p hg
    simpa only [d2075, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7248 (p : Pattern) (guard : d2076 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7231 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7249 (p : Pattern) (guard : d2077 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2076 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7248 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
