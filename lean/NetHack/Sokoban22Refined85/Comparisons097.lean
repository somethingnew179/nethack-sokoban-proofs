/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons096
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare13580 (p : Pattern) (guard : d4764 p = 1) : d1600 p ≤ (0 : Int) + d883 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1600, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13571 p hg
    simpa only [d1600, d883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1600, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13579 p hg
    simpa only [d1600, d883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13581 (p : Pattern) (guard : d0 p = 1) : d129 p ≤ (0 : Int) + d403 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13582 (p : Pattern) (guard : d4763 p = 1) : d1603 p ≤ (0 : Int) + d884 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1603, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12006 p hg
    simpa only [d4763, d1603, d884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1603, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13581 p hg
    simpa only [d4763, d1603, d884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13583 (p : Pattern) (guard : d4764 p = 1) : d1604 p ≤ (0 : Int) + d885 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1604, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13582 p hg
    simpa only [d4764, d1604, d885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1604, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13555 p hg
    simpa only [d4764, d1604, d885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13584 (p : Pattern) (guard : d0 p = 1) : d144 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13585 (p : Pattern) (guard : d4763 p = 1) : d1586 p ≤ (0 : Int) + d886 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1586, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11990 p hg
    simpa only [d4763, d1586, d886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1586, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13584 p hg
    simpa only [d4763, d1586, d886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13586 (p : Pattern) (guard : d4764 p = 1) : d1586 p ≤ (0 : Int) + d887 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13585 p hg
    simpa only [d4764, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13559 p hg
    simpa only [d4764, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13587 (p : Pattern) (guard : d4764 p = 1) : d1605 p ≤ (0 : Int) + d888 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1605, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13583 p hg
    simpa only [d1605, d888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1605, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13586 p hg
    simpa only [d1605, d888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13588 (p : Pattern) (guard : d0 p = 1) : d129 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13589 (p : Pattern) (guard : d4763 p = 1) : d1578 p ≤ (0 : Int) + d889 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1578, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11985 p hg
    simpa only [d4763, d1578, d889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1578, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13588 p hg
    simpa only [d4763, d1578, d889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13590 (p : Pattern) (guard : d4764 p = 1) : d1590 p ≤ (0 : Int) + d890 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1590, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13589 p hg
    simpa only [d4764, d1590, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1590, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13564 p hg
    simpa only [d4764, d1590, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13591 (p : Pattern) (guard : d4764 p = 1) : d1593 p ≤ (0 : Int) + d891 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1593, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13590 p hg
    simpa only [d1593, d891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1593, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13569 p hg
    simpa only [d1593, d891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13592 (p : Pattern) (guard : d4764 p = 1) : d1606 p ≤ (0 : Int) + d892 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1606, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13587 p hg
    simpa only [d1606, d892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1606, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13591 p hg
    simpa only [d1606, d892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13593 (p : Pattern) (guard : d4764 p = 1) : d1607 p ≤ (0 : Int) + d893 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1607, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13591 p hg
    simpa only [d1607, d893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1607, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7660 p hg
    simpa only [d1607, d893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13594 (p : Pattern) (guard : d4764 p = 1) : d1608 p ≤ (0 : Int) + d894 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1608, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13592 p hg
    simpa only [d1608, d894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1608, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13593 p hg
    simpa only [d1608, d894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13595 (p : Pattern) (guard : d4764 p = 1) : d1609 p ≤ (0 : Int) + d895 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1609, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13580 p hg
    simpa only [d1609, d895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1609, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13594 p hg
    simpa only [d1609, d895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13596 (p : Pattern) (guard : d4764 p = 1) : d1610 p ≤ (0 : Int) + d896 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1610, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13531 p hg
    simpa only [d1610, d896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1610, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13595 p hg
    simpa only [d1610, d896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13597 (p : Pattern) (guard : d4764 p = 1) : d1611 p ≤ (0 : Int) + d897 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1611, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13552 p hg
    simpa only [d1611, d897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1611, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13596 p hg
    simpa only [d1611, d897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13598 (p : Pattern) (guard : d0 p = 1) : d1613 p ≤ (0 : Int) + d826 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13599 (p : Pattern) (guard : d4764 p = 1) : d1614 p ≤ (0 : Int) + d849 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1614, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13501 p hg
    simpa only [d4764, d1614, d849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1614, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13598 p hg
    simpa only [d4764, d1614, d849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13600 (p : Pattern) (guard : d0 p = 1) : d1617 p ≤ (0 : Int) + d800 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13601 (p : Pattern) (guard : d4764 p = 1) : d1618 p ≤ (0 : Int) + d850 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1618, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13504 p hg
    simpa only [d4764, d1618, d850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1618, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13600 p hg
    simpa only [d4764, d1618, d850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13602 (p : Pattern) (guard : d4764 p = 1) : d1619 p ≤ (0 : Int) + d851 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1619, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13599 p hg
    simpa only [d1619, d851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1619, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13601 p hg
    simpa only [d1619, d851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13603 (p : Pattern) (guard : d0 p = 1) : d177 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13604 (p : Pattern) (guard : d4763 p = 1) : d1621 p ≤ (0 : Int) + d898 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1621, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12026 p hg
    simpa only [d4763, d1621, d898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1621, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13603 p hg
    simpa only [d4763, d1621, d898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13605 (p : Pattern) (guard : d0 p = 1) : d1625 p ≤ (0 : Int) + d900 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13606 (p : Pattern) (guard : d4764 p = 1) : d1626 p ≤ (0 : Int) + d901 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1626, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13604 p hg
    simpa only [d4764, d1626, d901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1626, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13605 p hg
    simpa only [d4764, d1626, d901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13607 (p : Pattern) (guard : d0 p = 1) : d184 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13608 (p : Pattern) (guard : d4763 p = 1) : d1629 p ≤ (0 : Int) + d902 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1629, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12032 p hg
    simpa only [d4763, d1629, d902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1629, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13607 p hg
    simpa only [d4763, d1629, d902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13609 (p : Pattern) (guard : d0 p = 1) : d1632 p ≤ (0 : Int) + d904 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13610 (p : Pattern) (guard : d4764 p = 1) : d1633 p ≤ (0 : Int) + d905 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1633, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13608 p hg
    simpa only [d4764, d1633, d905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1633, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13609 p hg
    simpa only [d4764, d1633, d905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13611 (p : Pattern) (guard : d4764 p = 1) : d1634 p ≤ (0 : Int) + d906 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1634, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13606 p hg
    simpa only [d1634, d906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1634, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13610 p hg
    simpa only [d1634, d906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13612 (p : Pattern) (guard : d4764 p = 1) : d1635 p ≤ (0 : Int) + d907 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1635, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13602 p hg
    simpa only [d1635, d907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1635, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13611 p hg
    simpa only [d1635, d907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13613 (p : Pattern) (guard : d4764 p = 1) : d1636 p ≤ (0 : Int) + d908 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1636, d908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13611 p hg
    simpa only [d1636, d908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1636, d908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7660 p hg
    simpa only [d1636, d908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13614 (p : Pattern) (guard : d4764 p = 1) : d1637 p ≤ (0 : Int) + d909 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1637, d909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13612 p hg
    simpa only [d1637, d909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1637, d909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13613 p hg
    simpa only [d1637, d909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13615 (p : Pattern) (guard : d4764 p = 1) : d1638 p ≤ (0 : Int) + d910 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1638, d910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13545 p hg
    simpa only [d1638, d910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1638, d910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13614 p hg
    simpa only [d1638, d910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13616 (p : Pattern) (guard : d4764 p = 1) : d1639 p ≤ (0 : Int) + d911 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1639, d911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13531 p hg
    simpa only [d1639, d911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1639, d911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13615 p hg
    simpa only [d1639, d911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13617 (p : Pattern) (guard : d0 p = 1) : d217 p ≤ (0 : Int) + d451 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13618 (p : Pattern) (guard : d4763 p = 1) : d1641 p ≤ (0 : Int) + d912 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1641, d912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12045 p hg
    simpa only [d4763, d1641, d912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1641, d912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13617 p hg
    simpa only [d4763, d1641, d912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13619 (p : Pattern) (guard : d0 p = 1) : d1643 p ≤ (0 : Int) + d865 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13620 (p : Pattern) (guard : d4764 p = 1) : d1644 p ≤ (0 : Int) + d913 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1644, d913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13618 p hg
    simpa only [d4764, d1644, d913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1644, d913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13619 p hg
    simpa only [d4764, d1644, d913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13621 (p : Pattern) (guard : d4764 p = 1) : d1645 p ≤ (0 : Int) + d914 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1645, d914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13556 p hg
    simpa only [d1645, d914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1645, d914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13620 p hg
    simpa only [d1645, d914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13622 (p : Pattern) (guard : d0 p = 1) : d217 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13623 (p : Pattern) (guard : d4763 p = 1) : d1643 p ≤ (0 : Int) + d915 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1643, d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12051 p hg
    simpa only [d4763, d1643, d915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1643, d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13622 p hg
    simpa only [d4763, d1643, d915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13624 (p : Pattern) (guard : d4764 p = 1) : d1646 p ≤ (0 : Int) + d916 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1646, d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13623 p hg
    simpa only [d4764, d1646, d916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1646, d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13568 p hg
    simpa only [d4764, d1646, d916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13625 (p : Pattern) (guard : d4764 p = 1) : d1647 p ≤ (0 : Int) + d917 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1647, d917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13565 p hg
    simpa only [d1647, d917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1647, d917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13624 p hg
    simpa only [d1647, d917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13626 (p : Pattern) (guard : d4764 p = 1) : d1648 p ≤ (0 : Int) + d918 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1648, d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13621 p hg
    simpa only [d1648, d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1648, d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13625 p hg
    simpa only [d1648, d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13627 (p : Pattern) (guard : d4764 p = 1) : d1647 p ≤ (0 : Int) + d919 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1647, d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13574 p hg
    simpa only [d1647, d919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1647, d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13624 p hg
    simpa only [d1647, d919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13628 (p : Pattern) (guard : d4764 p = 1) : d1649 p ≤ (0 : Int) + d920 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1649, d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13627 p hg
    simpa only [d1649, d920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1649, d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13578 p hg
    simpa only [d1649, d920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13629 (p : Pattern) (guard : d4764 p = 1) : d1650 p ≤ (0 : Int) + d921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1650, d921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13626 p hg
    simpa only [d1650, d921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1650, d921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13628 p hg
    simpa only [d1650, d921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13630 (p : Pattern) (guard : d0 p = 1) : d1652 p ≤ (0 : Int) + d923 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13631 (p : Pattern) (guard : d4764 p = 1) : d1653 p ≤ (0 : Int) + d924 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1653, d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13582 p hg
    simpa only [d4764, d1653, d924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1653, d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13630 p hg
    simpa only [d4764, d1653, d924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13632 (p : Pattern) (guard : d0 p = 1) : d1655 p ≤ (0 : Int) + d927 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13633 (p : Pattern) (guard : d4764 p = 1) : d1656 p ≤ (0 : Int) + d928 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1656, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13623 p hg
    simpa only [d4764, d1656, d928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1656, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13632 p hg
    simpa only [d4764, d1656, d928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13634 (p : Pattern) (guard : d4764 p = 1) : d1657 p ≤ (0 : Int) + d929 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1657, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13631 p hg
    simpa only [d1657, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1657, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13633 p hg
    simpa only [d1657, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13635 (p : Pattern) (guard : d4763 p = 1) : d1660 p ≤ (0 : Int) + d930 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1660, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12065 p hg
    simpa only [d4763, d1660, d930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1660, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13566 p hg
    simpa only [d4763, d1660, d930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13636 (p : Pattern) (guard : d0 p = 1) : d1591 p ≤ (0 : Int) + d931 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13637 (p : Pattern) (guard : d4764 p = 1) : d1661 p ≤ (0 : Int) + d932 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1661, d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13635 p hg
    simpa only [d4764, d1661, d932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1661, d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13636 p hg
    simpa only [d4764, d1661, d932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13638 (p : Pattern) (guard : d0 p = 1) : d231 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13639 (p : Pattern) (guard : d4763 p = 1) : d1652 p ≤ (0 : Int) + d931 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1652, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12068 p hg
    simpa only [d4763, d1652, d931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1652, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13638 p hg
    simpa only [d4763, d1652, d931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13640 (p : Pattern) (guard : d0 p = 1) : d1662 p ≤ (0 : Int) + d934 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13641 (p : Pattern) (guard : d4764 p = 1) : d1663 p ≤ (0 : Int) + d935 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1663, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13639 p hg
    simpa only [d4764, d1663, d935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1663, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13640 p hg
    simpa only [d4764, d1663, d935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13642 (p : Pattern) (guard : d4764 p = 1) : d1664 p ≤ (0 : Int) + d936 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1664, d936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13637 p hg
    simpa only [d1664, d936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1664, d936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13641 p hg
    simpa only [d1664, d936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13643 (p : Pattern) (guard : d4764 p = 1) : d1665 p ≤ (0 : Int) + d937 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1665, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13634 p hg
    simpa only [d1665, d937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1665, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13642 p hg
    simpa only [d1665, d937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13644 (p : Pattern) (guard : d0 p = 1) : d1669 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13645 (p : Pattern) (guard : d4763 p = 1) : d1670 p ≤ (0 : Int) + d938 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d1670, d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12078 p hg
    simpa only [d4763, d1670, d938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d1670, d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13644 p hg
    simpa only [d4763, d1670, d938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13646 (p : Pattern) (guard : d0 p = 1) : d1673 p ≤ (0 : Int) + d940 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13647 (p : Pattern) (guard : d4764 p = 1) : d1674 p ≤ (0 : Int) + d941 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d1674, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13645 p hg
    simpa only [d4764, d1674, d941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d1674, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13646 p hg
    simpa only [d4764, d1674, d941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13648 (p : Pattern) (guard : d4764 p = 1) : d1675 p ≤ (0 : Int) + d942 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1675, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13647 p hg
    simpa only [d1675, d942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1675, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13641 p hg
    simpa only [d1675, d942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13649 (p : Pattern) (guard : d4764 p = 1) : d1676 p ≤ (0 : Int) + d943 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1676, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13648 p hg
    simpa only [d1676, d943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1676, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7660 p hg
    simpa only [d1676, d943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13650 (p : Pattern) (guard : d4764 p = 1) : d1677 p ≤ (0 : Int) + d944 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1677, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13643 p hg
    simpa only [d1677, d944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1677, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13649 p hg
    simpa only [d1677, d944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13651 (p : Pattern) (guard : d4764 p = 1) : d1678 p ≤ (0 : Int) + d945 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1678, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13629 p hg
    simpa only [d1678, d945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1678, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13650 p hg
    simpa only [d1678, d945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13652 (p : Pattern) (guard : d4764 p = 1) : d1679 p ≤ (0 : Int) + d946 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1679, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13531 p hg
    simpa only [d1679, d946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1679, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13651 p hg
    simpa only [d1679, d946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13653 (p : Pattern) (guard : d4764 p = 1) : d1680 p ≤ (0 : Int) + d947 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1680, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13616 p hg
    simpa only [d1680, d947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1680, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13652 p hg
    simpa only [d1680, d947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13654 (p : Pattern) (guard : d4764 p = 1) : d1681 p ≤ (0 : Int) + d948 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d1681, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13597 p hg
    simpa only [d1681, d948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d1681, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13653 p hg
    simpa only [d1681, d948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13655 (p : Pattern) (guard : d4395 p = 1) : d1399 p ≤ (0 : Int) + d951 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1399, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7786 p hg
    simpa only [d4395, d1399, d951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1399, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4215 p hg
    simpa only [d4395, d1399, d951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13656 (p : Pattern) (guard : d4395 p = 1) : d1400 p ≤ (0 : Int) + d952 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1400, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6399 p hg
    simpa only [d1400, d952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1400, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13655 p hg
    simpa only [d1400, d952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13657 (p : Pattern) (guard : d4395 p = 1) : d1401 p ≤ (0 : Int) + d953 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1401, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4395, d1401, d953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1401, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4218 p hg
    simpa only [d4395, d1401, d953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13658 (p : Pattern) (guard : d4395 p = 1) : d50 p ≤ (0 : Int) + d954 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d50, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7792 p hg
    simpa only [d4395, d50, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d50, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4221 p hg
    simpa only [d4395, d50, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13659 (p : Pattern) (guard : d4395 p = 1) : d1402 p ≤ (0 : Int) + d955 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1402, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13657 p hg
    simpa only [d1402, d955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1402, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13658 p hg
    simpa only [d1402, d955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13660 (p : Pattern) (guard : d4395 p = 1) : d1403 p ≤ (0 : Int) + d956 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1403, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13656 p hg
    simpa only [d1403, d956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1403, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13659 p hg
    simpa only [d1403, d956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13661 (p : Pattern) (guard : d4395 p = 1) : d1404 p ≤ (0 : Int) + d957 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1404, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d1404, d957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1404, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d4395, d1404, d957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13662 (p : Pattern) (guard : d4395 p = 1) : d1405 p ≤ (0 : Int) + d958 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1405, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6412 p hg
    simpa only [d4395, d1405, d958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1405, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d4395, d1405, d958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13663 (p : Pattern) (guard : d4395 p = 1) : d1406 p ≤ (0 : Int) + d959 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1406, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13661 p hg
    simpa only [d1406, d959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1406, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13662 p hg
    simpa only [d1406, d959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13664 (p : Pattern) (guard : d4395 p = 1) : d1407 p ≤ (0 : Int) + d960 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1407, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6412 p hg
    simpa only [d4395, d1407, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1407, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d4395, d1407, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13665 (p : Pattern) (guard : d4395 p = 1) : d177 p ≤ (0 : Int) + d961 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d177, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7804 p hg
    simpa only [d4395, d177, d961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d177, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10096 p hg
    simpa only [d4395, d177, d961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13666 (p : Pattern) (guard : d4395 p = 1) : d1408 p ≤ (0 : Int) + d962 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1408, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d1408, d962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1408, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d1408, d962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13667 (p : Pattern) (guard : d4395 p = 1) : d1409 p ≤ (0 : Int) + d963 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1409, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13663 p hg
    simpa only [d1409, d963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1409, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d1409, d963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13668 (p : Pattern) (guard : d4395 p = 1) : d1410 p ≤ (0 : Int) + d964 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1410, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13660 p hg
    simpa only [d1410, d964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1410, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d1410, d964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13669 (p : Pattern) (guard : d4395 p = 1) : d1411 p ≤ (0 : Int) + d966 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1411, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d1411, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1411, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4229 p hg
    simpa only [d4395, d1411, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13670 (p : Pattern) (guard : d4395 p = 1) : d1412 p ≤ (0 : Int) + d967 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1412, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6419 p hg
    simpa only [d1412, d967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1412, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d1412, d967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13671 (p : Pattern) (guard : d4395 p = 1) : d1413 p ≤ (0 : Int) + d968 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1413, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4395, d1413, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1413, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d4395, d1413, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13672 (p : Pattern) (guard : d4395 p = 1) : d1414 p ≤ (0 : Int) + d969 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1414, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13671 p hg
    simpa only [d1414, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1414, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7817 p hg
    simpa only [d1414, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13673 (p : Pattern) (guard : d4395 p = 1) : d1415 p ≤ (0 : Int) + d970 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1415, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d1415, d970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1415, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d1415, d970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13674 (p : Pattern) (guard : d4395 p = 1) : d1416 p ≤ (0 : Int) + d971 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1416, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d1416, d971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1416, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10108 p hg
    simpa only [d4395, d1416, d971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13675 (p : Pattern) (guard : d4395 p = 1) : d1417 p ≤ (0 : Int) + d972 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1417, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6430 p hg
    simpa only [d4395, d1417, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1417, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d4395, d1417, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13676 (p : Pattern) (guard : d4395 p = 1) : d1418 p ≤ (0 : Int) + d973 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1418, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d1418, d973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1418, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13675 p hg
    simpa only [d1418, d973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13677 (p : Pattern) (guard : d4395 p = 1) : d1419 p ≤ (0 : Int) + d975 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1419, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13676 p hg
    simpa only [d1419, d975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1419, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7824 p hg
    simpa only [d1419, d975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13678 (p : Pattern) (guard : d4395 p = 1) : d1420 p ≤ (0 : Int) + d976 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1420, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13673 p hg
    simpa only [d1420, d976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1420, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13677 p hg
    simpa only [d1420, d976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13679 (p : Pattern) (guard : d4395 p = 1) : d1421 p ≤ (0 : Int) + d977 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1421, d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d1421, d977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1421, d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13678 p hg
    simpa only [d1421, d977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13680 (p : Pattern) (guard : d4395 p = 1) : d1412 p ≤ (0 : Int) + d979 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1412, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6437 p hg
    simpa only [d1412, d979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1412, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d1412, d979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13681 (p : Pattern) (guard : d4395 p = 1) : d1415 p ≤ (0 : Int) + d980 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1415, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d1415, d980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1415, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d1415, d980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13682 (p : Pattern) (guard : d4395 p = 1) : d1416 p ≤ (0 : Int) + d981 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1416, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d1416, d981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1416, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10121 p hg
    simpa only [d4395, d1416, d981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13683 (p : Pattern) (guard : d4395 p = 1) : d1418 p ≤ (0 : Int) + d982 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1418, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13682 p hg
    simpa only [d1418, d982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1418, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13675 p hg
    simpa only [d1418, d982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13684 (p : Pattern) (guard : d4395 p = 1) : d1419 p ≤ (0 : Int) + d983 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1419, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13683 p hg
    simpa only [d1419, d983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1419, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7824 p hg
    simpa only [d1419, d983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13685 (p : Pattern) (guard : d4395 p = 1) : d1420 p ≤ (0 : Int) + d984 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1420, d984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13681 p hg
    simpa only [d1420, d984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1420, d984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d1420, d984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13686 (p : Pattern) (guard : d4395 p = 1) : d92 p ≤ (0 : Int) + d986 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d92, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6448 p hg
    simpa only [d92, d986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d92, d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7838 p hg
    simpa only [d92, d986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13687 (p : Pattern) (guard : d4395 p = 1) : d94 p ≤ (0 : Int) + d987 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d94, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13686 p hg
    simpa only [d94, d987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d94, d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7840 p hg
    simpa only [d94, d987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13688 (p : Pattern) (guard : d4395 p = 1) : d96 p ≤ (0 : Int) + d988 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d96, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13687 p hg
    simpa only [d96, d988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d96, d988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7842 p hg
    simpa only [d96, d988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13689 (p : Pattern) (guard : d4395 p = 1) : d1422 p ≤ (0 : Int) + d989 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1422, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13685 p hg
    simpa only [d1422, d989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1422, d989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13688 p hg
    simpa only [d1422, d989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13690 (p : Pattern) (guard : d4395 p = 1) : d1423 p ≤ (0 : Int) + d990 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1423, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13679 p hg
    simpa only [d1423, d990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1423, d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13689 p hg
    simpa only [d1423, d990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13691 (p : Pattern) (guard : d4395 p = 1) : d1399 p ≤ (0 : Int) + d992 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1399, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7786 p hg
    simpa only [d4395, d1399, d992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1399, d992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4229 p hg
    simpa only [d4395, d1399, d992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13692 (p : Pattern) (guard : d4395 p = 1) : d1400 p ≤ (0 : Int) + d993 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1400, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6457 p hg
    simpa only [d1400, d993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1400, d993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13691 p hg
    simpa only [d1400, d993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13693 (p : Pattern) (guard : d4395 p = 1) : d1401 p ≤ (0 : Int) + d994 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1401, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4395, d1401, d994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1401, d994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4259 p hg
    simpa only [d4395, d1401, d994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13694 (p : Pattern) (guard : d4395 p = 1) : d1402 p ≤ (0 : Int) + d995 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1402, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13693 p hg
    simpa only [d1402, d995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1402, d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13658 p hg
    simpa only [d1402, d995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13695 (p : Pattern) (guard : d4395 p = 1) : d1403 p ≤ (0 : Int) + d996 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1403, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13692 p hg
    simpa only [d1403, d996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1403, d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13694 p hg
    simpa only [d1403, d996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13696 (p : Pattern) (guard : d4395 p = 1) : d1416 p ≤ (0 : Int) + d997 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1416, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d1416, d997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1416, d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10140 p hg
    simpa only [d4395, d1416, d997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13697 (p : Pattern) (guard : d4395 p = 1) : d1405 p ≤ (0 : Int) + d960 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1405, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6412 p hg
    simpa only [d4395, d1405, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1405, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d4395, d1405, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13698 (p : Pattern) (guard : d4395 p = 1) : d1424 p ≤ (0 : Int) + d998 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1424, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13696 p hg
    simpa only [d1424, d998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1424, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d1424, d998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13699 (p : Pattern) (guard : d4395 p = 1) : d1425 p ≤ (0 : Int) + d999 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1425, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d1425, d999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1425, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d1425, d999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13700 (p : Pattern) (guard : d4395 p = 1) : d1426 p ≤ (0 : Int) + d1000 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1426, d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13695 p hg
    simpa only [d1426, d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1426, d1000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13699 p hg
    simpa only [d1426, d1000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13701 (p : Pattern) (guard : d4395 p = 1) : d1412 p ≤ (0 : Int) + d1002 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1412, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6470 p hg
    simpa only [d1412, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1412, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d1412, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13702 (p : Pattern) (guard : d4395 p = 1) : d1415 p ≤ (0 : Int) + d1003 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1415, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13701 p hg
    simpa only [d1415, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1415, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d1415, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13703 (p : Pattern) (guard : d4395 p = 1) : d1416 p ≤ (0 : Int) + d966 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1416, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d1416, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1416, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10152 p hg
    simpa only [d4395, d1416, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13704 (p : Pattern) (guard : d4395 p = 1) : d1418 p ≤ (0 : Int) + d1004 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1418, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13703 p hg
    simpa only [d1418, d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1418, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13675 p hg
    simpa only [d1418, d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13705 (p : Pattern) (guard : d4395 p = 1) : d1419 p ≤ (0 : Int) + d1005 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1419, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13704 p hg
    simpa only [d1419, d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1419, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7824 p hg
    simpa only [d1419, d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13706 (p : Pattern) (guard : d4395 p = 1) : d1420 p ≤ (0 : Int) + d1006 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1420, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13702 p hg
    simpa only [d1420, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1420, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13705 p hg
    simpa only [d1420, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13707 (p : Pattern) (guard : d4395 p = 1) : d1427 p ≤ (0 : Int) + d1007 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1427, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d1427, d1007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1427, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13706 p hg
    simpa only [d1427, d1007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13708 (p : Pattern) (guard : d4395 p = 1) : d1412 p ≤ (0 : Int) + d1009 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1412, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6480 p hg
    simpa only [d1412, d1009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1412, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d1412, d1009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13709 (p : Pattern) (guard : d4395 p = 1) : d1415 p ≤ (0 : Int) + d1010 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1415, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13708 p hg
    simpa only [d1415, d1010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1415, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d1415, d1010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13710 (p : Pattern) (guard : d4395 p = 1) : d1420 p ≤ (0 : Int) + d1011 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1420, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13709 p hg
    simpa only [d1420, d1011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1420, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13705 p hg
    simpa only [d1420, d1011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13711 (p : Pattern) (guard : d4395 p = 1) : d1428 p ≤ (0 : Int) + d1012 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1428, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13710 p hg
    simpa only [d1428, d1012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1428, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7817 p hg
    simpa only [d1428, d1012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13712 (p : Pattern) (guard : d4395 p = 1) : d1429 p ≤ (0 : Int) + d1013 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1429, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13707 p hg
    simpa only [d1429, d1013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1429, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13711 p hg
    simpa only [d1429, d1013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13713 (p : Pattern) (guard : d4395 p = 1) : d1430 p ≤ (0 : Int) + d1014 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1430, d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13690 p hg
    simpa only [d1430, d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1430, d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13712 p hg
    simpa only [d1430, d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13714 (p : Pattern) (guard : d4395 p = 1) : d1399 p ≤ (0 : Int) + d1016 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1399, d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7786 p hg
    simpa only [d4395, d1399, d1016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1399, d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4284 p hg
    simpa only [d4395, d1399, d1016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13715 (p : Pattern) (guard : d4395 p = 1) : d1400 p ≤ (0 : Int) + d1017 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1400, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6488 p hg
    simpa only [d1400, d1017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1400, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13714 p hg
    simpa only [d1400, d1017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13716 (p : Pattern) (guard : d4395 p = 1) : d1401 p ≤ (0 : Int) + d1018 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1401, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4395, d1401, d1018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1401, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4287 p hg
    simpa only [d4395, d1401, d1018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13717 (p : Pattern) (guard : d4395 p = 1) : d1402 p ≤ (0 : Int) + d1019 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1402, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13716 p hg
    simpa only [d1402, d1019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1402, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13658 p hg
    simpa only [d1402, d1019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13718 (p : Pattern) (guard : d4395 p = 1) : d1403 p ≤ (0 : Int) + d1020 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d1403, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13715 p hg
    simpa only [d1403, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d1403, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13717 p hg
    simpa only [d1403, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13719 (p : Pattern) (guard : d4395 p = 1) : d1431 p ≤ (0 : Int) + d1021 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1431, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d1431, d1021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1431, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10174 p hg
    simpa only [d4395, d1431, d1021, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
