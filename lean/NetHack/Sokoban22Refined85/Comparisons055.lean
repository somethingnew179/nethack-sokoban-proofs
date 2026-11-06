/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons054
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7700 (p : Pattern) (guard : d4764 p = 1) : d876 p ≤ (0 : Int) + d1592 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d876, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7698 p hg
    simpa only [d4764, d876, d1592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d876, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7699 p hg
    simpa only [d4764, d876, d1592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7701 (p : Pattern) (guard : d4764 p = 1) : d877 p ≤ (0 : Int) + d1593 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d877, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7696 p hg
    simpa only [d877, d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d877, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7700 p hg
    simpa only [d877, d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7702 (p : Pattern) (guard : d4764 p = 1) : d878 p ≤ (0 : Int) + d1594 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d878, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7692 p hg
    simpa only [d878, d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d878, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7701 p hg
    simpa only [d878, d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7703 (p : Pattern) (guard : d0 p = 1) : d394 p ≤ (0 : Int) + d129 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7704 (p : Pattern) (guard : d4763 p = 1) : d879 p ≤ (0 : Int) + d1578 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d879, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5198 p hg
    simpa only [d4763, d879, d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d879, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7703 p hg
    simpa only [d4763, d879, d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7705 (p : Pattern) (guard : d4764 p = 1) : d880 p ≤ (0 : Int) + d1590 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d880, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7704 p hg
    simpa only [d4764, d880, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d880, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7695 p hg
    simpa only [d4764, d880, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7706 (p : Pattern) (guard : d4764 p = 1) : d881 p ≤ (0 : Int) + d1593 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d881, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7705 p hg
    simpa only [d881, d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d881, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7700 p hg
    simpa only [d881, d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7707 (p : Pattern) (guard : d4763 p = 1) : d160 p ≤ (0 : Int) + d1596 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d160, d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5214 p hg
    simpa only [d4763, d160, d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d160, d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4763, d160, d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7708 (p : Pattern) (guard : d4764 p = 1) : d161 p ≤ (0 : Int) + d1597 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d161, d1597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7707 p hg
    simpa only [d4764, d161, d1597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d161, d1597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4764, d161, d1597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7709 (p : Pattern) (guard : d4764 p = 1) : d162 p ≤ (0 : Int) + d1598 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d162, d1598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7708 p hg
    simpa only [d162, d1598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d162, d1598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7660 p hg
    simpa only [d162, d1598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7710 (p : Pattern) (guard : d4764 p = 1) : d882 p ≤ (0 : Int) + d1599 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d882, d1599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7706 p hg
    simpa only [d882, d1599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d882, d1599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7709 p hg
    simpa only [d882, d1599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7711 (p : Pattern) (guard : d4764 p = 1) : d883 p ≤ (0 : Int) + d1600 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d883, d1600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7702 p hg
    simpa only [d883, d1600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d883, d1600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7710 p hg
    simpa only [d883, d1600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7712 (p : Pattern) (guard : d0 p = 1) : d403 p ≤ (0 : Int) + d129 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7713 (p : Pattern) (guard : d4763 p = 1) : d884 p ≤ (0 : Int) + d1603 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d884, d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5221 p hg
    simpa only [d4763, d884, d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d884, d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7712 p hg
    simpa only [d4763, d884, d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7714 (p : Pattern) (guard : d4764 p = 1) : d885 p ≤ (0 : Int) + d1604 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d885, d1604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7713 p hg
    simpa only [d4764, d885, d1604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d885, d1604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7686 p hg
    simpa only [d4764, d885, d1604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7715 (p : Pattern) (guard : d0 p = 1) : d375 p ≤ (0 : Int) + d144 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7716 (p : Pattern) (guard : d4763 p = 1) : d886 p ≤ (0 : Int) + d1586 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d886, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5206 p hg
    simpa only [d4763, d886, d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d886, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7715 p hg
    simpa only [d4763, d886, d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7717 (p : Pattern) (guard : d4764 p = 1) : d887 p ≤ (0 : Int) + d1586 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7716 p hg
    simpa only [d4764, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7690 p hg
    simpa only [d4764, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7718 (p : Pattern) (guard : d4764 p = 1) : d888 p ≤ (0 : Int) + d1605 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d888, d1605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7714 p hg
    simpa only [d888, d1605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d888, d1605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7717 p hg
    simpa only [d888, d1605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7719 (p : Pattern) (guard : d4763 p = 1) : d889 p ≤ (0 : Int) + d1578 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d889, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5198 p hg
    simpa only [d4763, d889, d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d889, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7507 p hg
    simpa only [d4763, d889, d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7720 (p : Pattern) (guard : d4764 p = 1) : d890 p ≤ (0 : Int) + d1590 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d890, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7719 p hg
    simpa only [d4764, d890, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d890, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7695 p hg
    simpa only [d4764, d890, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7721 (p : Pattern) (guard : d4764 p = 1) : d891 p ≤ (0 : Int) + d1593 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d891, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7720 p hg
    simpa only [d891, d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d891, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7700 p hg
    simpa only [d891, d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7722 (p : Pattern) (guard : d4764 p = 1) : d892 p ≤ (0 : Int) + d1606 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d892, d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7718 p hg
    simpa only [d892, d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d892, d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7721 p hg
    simpa only [d892, d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7723 (p : Pattern) (guard : d4764 p = 1) : d893 p ≤ (0 : Int) + d1607 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d893, d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7721 p hg
    simpa only [d893, d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d893, d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7660 p hg
    simpa only [d893, d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7724 (p : Pattern) (guard : d4764 p = 1) : d894 p ≤ (0 : Int) + d1608 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d894, d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7722 p hg
    simpa only [d894, d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d894, d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7723 p hg
    simpa only [d894, d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7725 (p : Pattern) (guard : d4764 p = 1) : d895 p ≤ (0 : Int) + d1609 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d895, d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7711 p hg
    simpa only [d895, d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d895, d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7724 p hg
    simpa only [d895, d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7726 (p : Pattern) (guard : d4764 p = 1) : d896 p ≤ (0 : Int) + d1610 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d896, d1610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7663 p hg
    simpa only [d896, d1610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d896, d1610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7725 p hg
    simpa only [d896, d1610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7727 (p : Pattern) (guard : d4764 p = 1) : d897 p ≤ (0 : Int) + d1611 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d897, d1611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7683 p hg
    simpa only [d897, d1611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d897, d1611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7726 p hg
    simpa only [d897, d1611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7728 (p : Pattern) (guard : d0 p = 1) : d826 p ≤ (0 : Int) + d1613 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7729 (p : Pattern) (guard : d4764 p = 1) : d849 p ≤ (0 : Int) + d1614 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d849, d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7633 p hg
    simpa only [d4764, d849, d1614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d849, d1614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7728 p hg
    simpa only [d4764, d849, d1614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7730 (p : Pattern) (guard : d0 p = 1) : d800 p ≤ (0 : Int) + d1617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7731 (p : Pattern) (guard : d4764 p = 1) : d850 p ≤ (0 : Int) + d1618 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d850, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7636 p hg
    simpa only [d4764, d850, d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d850, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7730 p hg
    simpa only [d4764, d850, d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7732 (p : Pattern) (guard : d4764 p = 1) : d851 p ≤ (0 : Int) + d1619 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d851, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7729 p hg
    simpa only [d851, d1619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d851, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7731 p hg
    simpa only [d851, d1619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7733 (p : Pattern) (guard : d4763 p = 1) : d898 p ≤ (0 : Int) + d1621 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d898, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5248 p hg
    simpa only [d4763, d898, d1621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d898, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7428 p hg
    simpa only [d4763, d898, d1621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7734 (p : Pattern) (guard : d0 p = 1) : d900 p ≤ (0 : Int) + d1625 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7735 (p : Pattern) (guard : d4764 p = 1) : d901 p ≤ (0 : Int) + d1626 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d901, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7733 p hg
    simpa only [d4764, d901, d1626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d901, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7734 p hg
    simpa only [d4764, d901, d1626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7736 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d184 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7737 (p : Pattern) (guard : d4763 p = 1) : d902 p ≤ (0 : Int) + d1629 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d902, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5258 p hg
    simpa only [d4763, d902, d1629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d902, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7736 p hg
    simpa only [d4763, d902, d1629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7738 (p : Pattern) (guard : d0 p = 1) : d904 p ≤ (0 : Int) + d1632 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7739 (p : Pattern) (guard : d4764 p = 1) : d905 p ≤ (0 : Int) + d1633 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d905, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7737 p hg
    simpa only [d4764, d905, d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d905, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7738 p hg
    simpa only [d4764, d905, d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7740 (p : Pattern) (guard : d4764 p = 1) : d906 p ≤ (0 : Int) + d1634 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d906, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7735 p hg
    simpa only [d906, d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d906, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7739 p hg
    simpa only [d906, d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7741 (p : Pattern) (guard : d4764 p = 1) : d907 p ≤ (0 : Int) + d1635 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d907, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7732 p hg
    simpa only [d907, d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d907, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7740 p hg
    simpa only [d907, d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7742 (p : Pattern) (guard : d4764 p = 1) : d908 p ≤ (0 : Int) + d1636 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d908, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7740 p hg
    simpa only [d908, d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d908, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7660 p hg
    simpa only [d908, d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7743 (p : Pattern) (guard : d4764 p = 1) : d909 p ≤ (0 : Int) + d1637 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d909, d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7741 p hg
    simpa only [d909, d1637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d909, d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7742 p hg
    simpa only [d909, d1637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7744 (p : Pattern) (guard : d4764 p = 1) : d910 p ≤ (0 : Int) + d1638 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d910, d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7676 p hg
    simpa only [d910, d1638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d910, d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7743 p hg
    simpa only [d910, d1638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7745 (p : Pattern) (guard : d4764 p = 1) : d911 p ≤ (0 : Int) + d1639 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d911, d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7663 p hg
    simpa only [d911, d1639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d911, d1639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7744 p hg
    simpa only [d911, d1639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7746 (p : Pattern) (guard : d0 p = 1) : d451 p ≤ (0 : Int) + d217 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7747 (p : Pattern) (guard : d4763 p = 1) : d912 p ≤ (0 : Int) + d1641 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d912, d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5271 p hg
    simpa only [d4763, d912, d1641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d912, d1641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7746 p hg
    simpa only [d4763, d912, d1641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7748 (p : Pattern) (guard : d0 p = 1) : d865 p ≤ (0 : Int) + d1643 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7749 (p : Pattern) (guard : d4764 p = 1) : d913 p ≤ (0 : Int) + d1644 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d913, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7747 p hg
    simpa only [d4764, d913, d1644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d913, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7748 p hg
    simpa only [d4764, d913, d1644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7750 (p : Pattern) (guard : d4764 p = 1) : d914 p ≤ (0 : Int) + d1645 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d914, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7687 p hg
    simpa only [d914, d1645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d914, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7749 p hg
    simpa only [d914, d1645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7751 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d217 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7752 (p : Pattern) (guard : d4763 p = 1) : d915 p ≤ (0 : Int) + d1643 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d915, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5280 p hg
    simpa only [d4763, d915, d1643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d915, d1643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7751 p hg
    simpa only [d4763, d915, d1643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7753 (p : Pattern) (guard : d4764 p = 1) : d916 p ≤ (0 : Int) + d1646 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d916, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7752 p hg
    simpa only [d4764, d916, d1646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d916, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7699 p hg
    simpa only [d4764, d916, d1646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7754 (p : Pattern) (guard : d4764 p = 1) : d917 p ≤ (0 : Int) + d1647 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d917, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7696 p hg
    simpa only [d917, d1647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d917, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7753 p hg
    simpa only [d917, d1647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7755 (p : Pattern) (guard : d4764 p = 1) : d918 p ≤ (0 : Int) + d1648 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d918, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7750 p hg
    simpa only [d918, d1648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d918, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7754 p hg
    simpa only [d918, d1648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7756 (p : Pattern) (guard : d4764 p = 1) : d919 p ≤ (0 : Int) + d1647 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d919, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7705 p hg
    simpa only [d919, d1647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d919, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7753 p hg
    simpa only [d919, d1647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7757 (p : Pattern) (guard : d4764 p = 1) : d920 p ≤ (0 : Int) + d1649 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d920, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7756 p hg
    simpa only [d920, d1649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d920, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7709 p hg
    simpa only [d920, d1649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7758 (p : Pattern) (guard : d4764 p = 1) : d921 p ≤ (0 : Int) + d1650 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d921, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7755 p hg
    simpa only [d921, d1650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d921, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7757 p hg
    simpa only [d921, d1650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7759 (p : Pattern) (guard : d0 p = 1) : d923 p ≤ (0 : Int) + d1652 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7760 (p : Pattern) (guard : d4764 p = 1) : d924 p ≤ (0 : Int) + d1653 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d924, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7713 p hg
    simpa only [d4764, d924, d1653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d924, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7759 p hg
    simpa only [d4764, d924, d1653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7761 (p : Pattern) (guard : d0 p = 1) : d927 p ≤ (0 : Int) + d1655 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7762 (p : Pattern) (guard : d4764 p = 1) : d928 p ≤ (0 : Int) + d1656 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d928, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7752 p hg
    simpa only [d4764, d928, d1656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d928, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7761 p hg
    simpa only [d4764, d928, d1656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7763 (p : Pattern) (guard : d4764 p = 1) : d929 p ≤ (0 : Int) + d1657 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d929, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7760 p hg
    simpa only [d929, d1657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d929, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7762 p hg
    simpa only [d929, d1657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7764 (p : Pattern) (guard : d4763 p = 1) : d930 p ≤ (0 : Int) + d1660 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d930, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5303 p hg
    simpa only [d4763, d930, d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d930, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7697 p hg
    simpa only [d4763, d930, d1660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7765 (p : Pattern) (guard : d0 p = 1) : d931 p ≤ (0 : Int) + d1591 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7766 (p : Pattern) (guard : d4764 p = 1) : d932 p ≤ (0 : Int) + d1661 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d932, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7764 p hg
    simpa only [d4764, d932, d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d932, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7765 p hg
    simpa only [d4764, d932, d1661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7767 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d231 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7768 (p : Pattern) (guard : d4763 p = 1) : d931 p ≤ (0 : Int) + d1652 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d931, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5306 p hg
    simpa only [d4763, d931, d1652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d931, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7767 p hg
    simpa only [d4763, d931, d1652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7769 (p : Pattern) (guard : d0 p = 1) : d934 p ≤ (0 : Int) + d1662 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7770 (p : Pattern) (guard : d4764 p = 1) : d935 p ≤ (0 : Int) + d1663 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d935, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7768 p hg
    simpa only [d4764, d935, d1663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d935, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7769 p hg
    simpa only [d4764, d935, d1663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7771 (p : Pattern) (guard : d4764 p = 1) : d936 p ≤ (0 : Int) + d1664 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d936, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7766 p hg
    simpa only [d936, d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d936, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7770 p hg
    simpa only [d936, d1664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7772 (p : Pattern) (guard : d4764 p = 1) : d937 p ≤ (0 : Int) + d1665 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d937, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7763 p hg
    simpa only [d937, d1665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d937, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7771 p hg
    simpa only [d937, d1665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7773 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1669 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7774 (p : Pattern) (guard : d4763 p = 1) : d938 p ≤ (0 : Int) + d1670 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4763, d938, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5314 p hg
    simpa only [d4763, d938, d1670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4763, d938, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7773 p hg
    simpa only [d4763, d938, d1670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7775 (p : Pattern) (guard : d0 p = 1) : d940 p ≤ (0 : Int) + d1673 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7776 (p : Pattern) (guard : d4764 p = 1) : d941 p ≤ (0 : Int) + d1674 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4763 p = 1 := by simpa only [d4764, d941, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7774 p hg
    simpa only [d4764, d941, d1674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4764, d941, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7775 p hg
    simpa only [d4764, d941, d1674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7777 (p : Pattern) (guard : d4764 p = 1) : d942 p ≤ (0 : Int) + d1675 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d942, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7776 p hg
    simpa only [d942, d1675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d942, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7770 p hg
    simpa only [d942, d1675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7778 (p : Pattern) (guard : d4764 p = 1) : d943 p ≤ (0 : Int) + d1676 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d943, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7777 p hg
    simpa only [d943, d1676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d943, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7660 p hg
    simpa only [d943, d1676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7779 (p : Pattern) (guard : d4764 p = 1) : d944 p ≤ (0 : Int) + d1677 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d944, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7772 p hg
    simpa only [d944, d1677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d944, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7778 p hg
    simpa only [d944, d1677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7780 (p : Pattern) (guard : d4764 p = 1) : d945 p ≤ (0 : Int) + d1678 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d945, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7758 p hg
    simpa only [d945, d1678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d945, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7779 p hg
    simpa only [d945, d1678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7781 (p : Pattern) (guard : d4764 p = 1) : d946 p ≤ (0 : Int) + d1679 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d946, d1679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7663 p hg
    simpa only [d946, d1679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d946, d1679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7780 p hg
    simpa only [d946, d1679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7782 (p : Pattern) (guard : d4764 p = 1) : d947 p ≤ (0 : Int) + d1680 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d947, d1680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7745 p hg
    simpa only [d947, d1680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d947, d1680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7781 p hg
    simpa only [d947, d1680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7783 (p : Pattern) (guard : d4764 p = 1) : d948 p ≤ (0 : Int) + d1681 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4764 p = 1 := by simpa only [d948, d1681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7727 p hg
    simpa only [d948, d1681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4764 p = 1 := by simpa only [d948, d1681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7782 p hg
    simpa only [d948, d1681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7784 (p : Pattern) (guard : d0 p = 1) : d346 p ≤ (0 : Int) + d21 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7785 (p : Pattern) (guard : d4395 p = 1) : d949 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d949, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d949, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d949, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7784 p hg
    simpa only [d4395, d949, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7786 (p : Pattern) (guard : d1 p = 1) : d950 p ≤ (0 : Int) + d950 p := by
  omega
theorem compare7787 (p : Pattern) (guard : d0 p = 1) : d361 p ≤ (0 : Int) + d27 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7788 (p : Pattern) (guard : d4395 p = 1) : d951 p ≤ (0 : Int) + d1399 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d951, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7786 p hg
    simpa only [d4395, d951, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d951, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7787 p hg
    simpa only [d4395, d951, d1399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7789 (p : Pattern) (guard : d4395 p = 1) : d952 p ≤ (0 : Int) + d1400 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d952, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7785 p hg
    simpa only [d952, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d952, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7788 p hg
    simpa only [d952, d1400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7790 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (0 : Int) + d44 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7791 (p : Pattern) (guard : d4395 p = 1) : d953 p ≤ (0 : Int) + d1401 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d953, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d4395, d953, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d953, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7790 p hg
    simpa only [d4395, d953, d1401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7792 (p : Pattern) (guard : d1 p = 1) : d47 p ≤ (0 : Int) + d47 p := by
  omega
theorem compare7793 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d49 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7794 (p : Pattern) (guard : d4395 p = 1) : d954 p ≤ (0 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d954, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7792 p hg
    simpa only [d4395, d954, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d954, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7793 p hg
    simpa only [d4395, d954, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7795 (p : Pattern) (guard : d4395 p = 1) : d955 p ≤ (0 : Int) + d1402 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d955, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7791 p hg
    simpa only [d955, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d955, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7794 p hg
    simpa only [d955, d1402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7796 (p : Pattern) (guard : d4395 p = 1) : d956 p ≤ (0 : Int) + d1403 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d956, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7789 p hg
    simpa only [d956, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d956, d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7795 p hg
    simpa only [d956, d1403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7797 (p : Pattern) (guard : d0 p = 1) : d369 p ≤ (0 : Int) + d1165 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7798 (p : Pattern) (guard : d4395 p = 1) : d957 p ≤ (0 : Int) + d1404 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d957, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d957, d1404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d957, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7797 p hg
    simpa only [d4395, d957, d1404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7799 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (0 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7800 (p : Pattern) (guard : d4395 p = 1) : d958 p ≤ (0 : Int) + d1405 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d958, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6412 p hg
    simpa only [d4395, d958, d1405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d958, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7799 p hg
    simpa only [d4395, d958, d1405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7801 (p : Pattern) (guard : d4395 p = 1) : d959 p ≤ (0 : Int) + d1406 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d959, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7798 p hg
    simpa only [d959, d1406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d959, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7800 p hg
    simpa only [d959, d1406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7802 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1171 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7803 (p : Pattern) (guard : d4395 p = 1) : d960 p ≤ (0 : Int) + d1407 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d960, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6412 p hg
    simpa only [d4395, d960, d1407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d960, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7802 p hg
    simpa only [d4395, d960, d1407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7804 (p : Pattern) (guard : d1 p = 1) : d176 p ≤ (0 : Int) + d176 p := by
  omega
theorem compare7805 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d73 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7806 (p : Pattern) (guard : d4395 p = 1) : d961 p ≤ (0 : Int) + d177 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d961, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7804 p hg
    simpa only [d4395, d961, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d961, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7805 p hg
    simpa only [d4395, d961, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7807 (p : Pattern) (guard : d4395 p = 1) : d962 p ≤ (0 : Int) + d1408 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d962, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7803 p hg
    simpa only [d962, d1408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d962, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7806 p hg
    simpa only [d962, d1408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7808 (p : Pattern) (guard : d4395 p = 1) : d963 p ≤ (0 : Int) + d1409 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d963, d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7801 p hg
    simpa only [d963, d1409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d963, d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7807 p hg
    simpa only [d963, d1409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7809 (p : Pattern) (guard : d4395 p = 1) : d964 p ≤ (0 : Int) + d1410 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d964, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7796 p hg
    simpa only [d964, d1410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d964, d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7808 p hg
    simpa only [d964, d1410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7810 (p : Pattern) (guard : d0 p = 1) : d361 p ≤ (0 : Int) + d21 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7811 (p : Pattern) (guard : d4395 p = 1) : d965 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d965, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d965, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d965, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7810 p hg
    simpa only [d4395, d965, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7812 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d27 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7813 (p : Pattern) (guard : d4395 p = 1) : d966 p ≤ (0 : Int) + d1411 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d966, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d966, d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d966, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7812 p hg
    simpa only [d4395, d966, d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7814 (p : Pattern) (guard : d4395 p = 1) : d967 p ≤ (0 : Int) + d1412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d967, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7811 p hg
    simpa only [d967, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d967, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7813 p hg
    simpa only [d967, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7815 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7816 (p : Pattern) (guard : d4395 p = 1) : d968 p ≤ (0 : Int) + d1413 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d968, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d4395, d968, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d968, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7815 p hg
    simpa only [d4395, d968, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7817 (p : Pattern) (guard : d4395 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare7818 (p : Pattern) (guard : d4395 p = 1) : d969 p ≤ (0 : Int) + d1414 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d969, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7816 p hg
    simpa only [d969, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d969, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7817 p hg
    simpa only [d969, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7819 (p : Pattern) (guard : d4395 p = 1) : d970 p ≤ (0 : Int) + d1415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d970, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7814 p hg
    simpa only [d970, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d970, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7818 p hg
    simpa only [d970, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7820 (p : Pattern) (guard : d0 p = 1) : d374 p ≤ (0 : Int) + d1181 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7821 (p : Pattern) (guard : d4395 p = 1) : d971 p ≤ (0 : Int) + d1416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d971, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d971, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d971, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7820 p hg
    simpa only [d4395, d971, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7822 (p : Pattern) (guard : d4395 p = 1) : d972 p ≤ (0 : Int) + d1417 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d972, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6430 p hg
    simpa only [d4395, d972, d1417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d972, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7815 p hg
    simpa only [d4395, d972, d1417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7823 (p : Pattern) (guard : d4395 p = 1) : d973 p ≤ (0 : Int) + d1418 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d973, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7821 p hg
    simpa only [d973, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d973, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7822 p hg
    simpa only [d973, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7824 (p : Pattern) (guard : d4395 p = 1) : d974 p ≤ (0 : Int) + d974 p := by
  omega
theorem compare7825 (p : Pattern) (guard : d4395 p = 1) : d975 p ≤ (0 : Int) + d1419 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d975, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7823 p hg
    simpa only [d975, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d975, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7824 p hg
    simpa only [d975, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7826 (p : Pattern) (guard : d4395 p = 1) : d976 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d976, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7819 p hg
    simpa only [d976, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d976, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7825 p hg
    simpa only [d976, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7827 (p : Pattern) (guard : d4395 p = 1) : d977 p ≤ (0 : Int) + d1421 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d977, d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7809 p hg
    simpa only [d977, d1421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d977, d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7826 p hg
    simpa only [d977, d1421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7828 (p : Pattern) (guard : d0 p = 1) : d389 p ≤ (0 : Int) + d21 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7829 (p : Pattern) (guard : d4395 p = 1) : d978 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d978, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4395, d978, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d978, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7828 p hg
    simpa only [d4395, d978, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7830 (p : Pattern) (guard : d4395 p = 1) : d979 p ≤ (0 : Int) + d1412 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d979, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7829 p hg
    simpa only [d979, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d979, d1412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7813 p hg
    simpa only [d979, d1412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7831 (p : Pattern) (guard : d4395 p = 1) : d980 p ≤ (0 : Int) + d1415 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d980, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7830 p hg
    simpa only [d980, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d980, d1415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7818 p hg
    simpa only [d980, d1415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7832 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (0 : Int) + d1181 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7833 (p : Pattern) (guard : d4395 p = 1) : d981 p ≤ (0 : Int) + d1416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d981, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6407 p hg
    simpa only [d4395, d981, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d981, d1416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7832 p hg
    simpa only [d4395, d981, d1416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7834 (p : Pattern) (guard : d4395 p = 1) : d982 p ≤ (0 : Int) + d1418 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d982, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7833 p hg
    simpa only [d982, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d982, d1418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7822 p hg
    simpa only [d982, d1418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7835 (p : Pattern) (guard : d4395 p = 1) : d983 p ≤ (0 : Int) + d1419 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d983, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7834 p hg
    simpa only [d983, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d983, d1419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7824 p hg
    simpa only [d983, d1419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7836 (p : Pattern) (guard : d4395 p = 1) : d984 p ≤ (0 : Int) + d1420 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d984, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7831 p hg
    simpa only [d984, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d984, d1420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7835 p hg
    simpa only [d984, d1420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7837 (p : Pattern) (guard : d4395 p = 1) : d985 p ≤ (0 : Int) + d90 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d985, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6447 p hg
    simpa only [d4395, d985, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d985, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7815 p hg
    simpa only [d4395, d985, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7838 (p : Pattern) (guard : d4395 p = 1) : d91 p ≤ (0 : Int) + d91 p := by
  omega
theorem compare7839 (p : Pattern) (guard : d4395 p = 1) : d986 p ≤ (0 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4395 p = 1 := by simpa only [d986, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7837 p hg
    simpa only [d986, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d986, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7838 p hg
    simpa only [d986, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
