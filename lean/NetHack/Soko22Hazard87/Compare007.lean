import NetHack.Soko22Hazard87.Compare006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare1750 (p : Pattern) (guard : d1596 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1595 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1749 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1166 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1751 (p : Pattern) (guard : d1597 p = 1) : d47797 p ≤ (-1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1596 p = 1 := by simpa only [d1597, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1750 p hg
    simpa only [d1597, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1597, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d1597, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1752 (p : Pattern) (guard : d1884 p = 1) : d47798 p ≤ (-1 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1883 p = 1 := by simpa only [d1884, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1746 p hg
    simpa only [d1884, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1597 p = 1 := by simpa only [d1884, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1751 p hg
    simpa only [d1884, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1753 (p : Pattern) (guard : d60788 p = 1) : d47799 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1884 p = 1 := by simpa only [d60788, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1752 p hg
    simpa only [d60788, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60788, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d60788, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1754 (p : Pattern) (guard : d60789 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d60788 p = 1 := by simpa only [d60789, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1753 p hg
    simpa only [d60789, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60789, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d60789, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1755 (p : Pattern) (guard : d60790 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d60789 p = 1 := by simpa only [d60790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1754 p hg
    simpa only [d60790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1175 p hg
    simpa only [d60790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1756 (p : Pattern) (guard : d60791 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d18190 p = 1 := by simpa only [d60791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1737 p hg
    simpa only [d60791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60790 p = 1 := by simpa only [d60791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1755 p hg
    simpa only [d60791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1757 (p : Pattern) (guard : d60792 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60783 p = 1 := by simpa only [d60792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1738 p hg
    simpa only [d60792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60791 p = 1 := by simpa only [d60792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1756 p hg
    simpa only [d60792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1758 (p : Pattern) (guard : d60793 p = 1) : d47804 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60793, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1135 p hg
    simpa only [d60793, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60792 p = 1 := by simpa only [d60793, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1757 p hg
    simpa only [d60793, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1759 (p : Pattern) (guard : d60794 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60794, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1134 p hg
    simpa only [d60794, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60793 p = 1 := by simpa only [d60794, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1758 p hg
    simpa only [d60794, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1760 (p : Pattern) (guard : d60795 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60786 p = 1 := by simpa only [d60795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1741 p hg
    simpa only [d60795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60794 p = 1 := by simpa only [d60795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1759 p hg
    simpa only [d60795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1761 (p : Pattern) (guard : d60800 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60794 p = 1 := by simpa only [d60800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1759 p hg
    simpa only [d60800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d60800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1762 (p : Pattern) (guard : d60801 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60795 p = 1 := by simpa only [d60801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1760 p hg
    simpa only [d60801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60800 p = 1 := by simpa only [d60801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1761 p hg
    simpa only [d60801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1763 (p : Pattern) (guard : d60802 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60801 p = 1 := by simpa only [d60802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1762 p hg
    simpa only [d60802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d60802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1764 (p : Pattern) (guard : d60803 p = 1) : d47807 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60802 p = 1 := by simpa only [d60803, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1763 p hg
    simpa only [d60803, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60803, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1185 p hg
    simpa only [d60803, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1765 (p : Pattern) (guard : d60804 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60804, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d60804, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60803 p = 1 := by simpa only [d60804, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1764 p hg
    simpa only [d60804, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1766 (p : Pattern) (guard : d60809 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60800 p = 1 := by simpa only [d60809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1761 p hg
    simpa only [d60809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d60809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1767 (p : Pattern) (guard : d60810 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60809 p = 1 := by simpa only [d60810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1766 p hg
    simpa only [d60810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d60810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1768 (p : Pattern) (guard : d60811 p = 1) : d47807 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60810 p = 1 := by simpa only [d60811, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1767 p hg
    simpa only [d60811, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60811, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1185 p hg
    simpa only [d60811, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1769 (p : Pattern) (guard : d60812 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60812, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d60812, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60811 p = 1 := by simpa only [d60812, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1768 p hg
    simpa only [d60812, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1770 (p : Pattern) (guard : d60813 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60804 p = 1 := by simpa only [d60813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1765 p hg
    simpa only [d60813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60812 p = 1 := by simpa only [d60813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1769 p hg
    simpa only [d60813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1771 (p : Pattern) (guard : d60814 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60813 p = 1 := by simpa only [d60814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1770 p hg
    simpa only [d60814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1772 (p : Pattern) (guard : d60815 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60814 p = 1 := by simpa only [d60815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1771 p hg
    simpa only [d60815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1773 (p : Pattern) (guard : d60816 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60815 p = 1 := by simpa only [d60816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1772 p hg
    simpa only [d60816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1774 (p : Pattern) (guard : d60826 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60812 p = 1 := by simpa only [d60826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1769 p hg
    simpa only [d60826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1775 (p : Pattern) (guard : d60827 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60826 p = 1 := by simpa only [d60827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1774 p hg
    simpa only [d60827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1776 (p : Pattern) (guard : d60828 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60827 p = 1 := by simpa only [d60828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1775 p hg
    simpa only [d60828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1777 (p : Pattern) (guard : d60829 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60828 p = 1 := by simpa only [d60829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1776 p hg
    simpa only [d60829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1778 (p : Pattern) (guard : d61166 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60816 p = 1 := by simpa only [d61166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1773 p hg
    simpa only [d61166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60829 p = 1 := by simpa only [d61166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1777 p hg
    simpa only [d61166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1779 (p : Pattern) (guard : d61167 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61166 p = 1 := by simpa only [d61167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1778 p hg
    simpa only [d61167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1780 (p : Pattern) (guard : d61168 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d61167 p = 1 := by simpa only [d61168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1779 p hg
    simpa only [d61168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1781 (p : Pattern) (guard : d61169 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61168 p = 1 := by simpa only [d61169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1780 p hg
    simpa only [d61169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1782 (p : Pattern) (guard : d61170 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61169 p = 1 := by simpa only [d61170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1781 p hg
    simpa only [d61170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1783 (p : Pattern) (guard : d61171 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61171, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d61171, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61170 p = 1 := by simpa only [d61171, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1782 p hg
    simpa only [d61171, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1784 (p : Pattern) (guard : d61172 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61171 p = 1 := by simpa only [d61172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1783 p hg
    simpa only [d61172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1785 (p : Pattern) (guard : d61173 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d61172 p = 1 := by simpa only [d61173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1784 p hg
    simpa only [d61173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1786 (p : Pattern) (guard : d61174 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d61173 p = 1 := by simpa only [d61174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1785 p hg
    simpa only [d61174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1787 (p : Pattern) (guard : d61175 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d61174 p = 1 := by simpa only [d61175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1786 p hg
    simpa only [d61175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1788 (p : Pattern) (guard : d61176 p = 1) : d47865 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d61175 p = 1 := by simpa only [d61176, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1787 p hg
    simpa only [d61176, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61176, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1202 p hg
    simpa only [d61176, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1789 (p : Pattern) (guard : d61177 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61177, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1129 p hg
    simpa only [d61177, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61176 p = 1 := by simpa only [d61177, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1788 p hg
    simpa only [d61177, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1790 (p : Pattern) (guard : d61178 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61177 p = 1 := by simpa only [d61178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1789 p hg
    simpa only [d61178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1791 (p : Pattern) (guard : d61179 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61178 p = 1 := by simpa only [d61179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1790 p hg
    simpa only [d61179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1792 (p : Pattern) (guard : d61180 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61179 p = 1 := by simpa only [d61180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1791 p hg
    simpa only [d61180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1793 (p : Pattern) (guard : d61181 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61180 p = 1 := by simpa only [d61181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1792 p hg
    simpa only [d61181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1794 (p : Pattern) (guard : d61182 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61181 p = 1 := by simpa only [d61182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1793 p hg
    simpa only [d61182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1795 (p : Pattern) (guard : d61183 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61182 p = 1 := by simpa only [d61183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1794 p hg
    simpa only [d61183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1796 (p : Pattern) (guard : d61184 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61183 p = 1 := by simpa only [d61184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1795 p hg
    simpa only [d61184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1797 (p : Pattern) (guard : d61185 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61184 p = 1 := by simpa only [d61185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1796 p hg
    simpa only [d61185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1798 (p : Pattern) (guard : d61186 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61185 p = 1 := by simpa only [d61186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1797 p hg
    simpa only [d61186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1799 (p : Pattern) (guard : d61187 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d61165 p = 1 := by simpa only [d61187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1596 p hg
    simpa only [d61187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61186 p = 1 := by simpa only [d61187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1798 p hg
    simpa only [d61187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1800 (p : Pattern) (guard : d1997 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d1997, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1138 p hg
    simpa only [d1997, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1801 (p : Pattern) (guard : d1998 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1800 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1802 (p : Pattern) (guard : d1999 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1801 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1803 (p : Pattern) (guard : d2000 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1802 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1804 (p : Pattern) (guard : d2001 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1523 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1605 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1805 (p : Pattern) (guard : d2002 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2001 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1804 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1806 (p : Pattern) (guard : d2003 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2002 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1805 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1807 (p : Pattern) (guard : d2004 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1803 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2003 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1806 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1808 (p : Pattern) (guard : d2005 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1605 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1809 (p : Pattern) (guard : d2006 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1808 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1810 (p : Pattern) (guard : d2007 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1809 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1811 (p : Pattern) (guard : d2008 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2007 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1810 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1812 (p : Pattern) (guard : d2009 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2004 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1807 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2008 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1811 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1813 (p : Pattern) (guard : d2010 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2009 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1812 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1814 (p : Pattern) (guard : d2011 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2010 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1813 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1815 (p : Pattern) (guard : d2012 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2011 p = 1 := by simpa only [d2012, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1814 p hg
    simpa only [d2012, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2012, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d2012, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1816 (p : Pattern) (guard : d2013 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1800 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1817 (p : Pattern) (guard : d2014 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1801 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1816 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1818 (p : Pattern) (guard : d2015 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1999 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1802 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1817 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1819 (p : Pattern) (guard : d2016 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d2016, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1210 p hg
    simpa only [d2016, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2016, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1138 p hg
    simpa only [d2016, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1820 (p : Pattern) (guard : d2017 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1800 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2016 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1819 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1821 (p : Pattern) (guard : d2018 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2017 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1820 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1822 (p : Pattern) (guard : d2019 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1805 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2018 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1821 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1823 (p : Pattern) (guard : d2020 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2015 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1818 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2019 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1822 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1824 (p : Pattern) (guard : d2021 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d2016 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1819 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1825 (p : Pattern) (guard : d2022 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2021 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1824 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1826 (p : Pattern) (guard : d2023 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1809 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2022 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1825 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1827 (p : Pattern) (guard : d2024 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2023 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1826 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1828 (p : Pattern) (guard : d2025 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2020 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1823 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2024 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1827 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1829 (p : Pattern) (guard : d2026 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2009 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1812 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2025 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1828 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1830 (p : Pattern) (guard : d2027 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1816 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1831 (p : Pattern) (guard : d2028 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1830 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1832 (p : Pattern) (guard : d2029 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1831 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1833 (p : Pattern) (guard : d2030 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1832 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1834 (p : Pattern) (guard : d2031 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1833 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1835 (p : Pattern) (guard : d2032 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2026 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1829 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1834 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1836 (p : Pattern) (guard : d2033 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2032 p = 1 := by simpa only [d2033, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1835 p hg
    simpa only [d2033, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2033, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d2033, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1837 (p : Pattern) (guard : d2034 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2012 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1815 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2033 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1836 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1838 (p : Pattern) (guard : d2335 p = 1) : d47652 p ≤ (-1 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2335, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d2335, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2034 p = 1 := by simpa only [d2335, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1837 p hg
    simpa only [d2335, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1839 (p : Pattern) (guard : d1997 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1288 p hg
    simpa only [d1997, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1154 p hg
    simpa only [d1997, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1840 (p : Pattern) (guard : d1998 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1839 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1841 (p : Pattern) (guard : d1999 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1840 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1842 (p : Pattern) (guard : d2000 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1841 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1843 (p : Pattern) (guard : d2001 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1523 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1649 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1844 (p : Pattern) (guard : d2002 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2001 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1843 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1845 (p : Pattern) (guard : d2003 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2002 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1844 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1846 (p : Pattern) (guard : d2004 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1842 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2003 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1845 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1847 (p : Pattern) (guard : d2005 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1649 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1848 (p : Pattern) (guard : d2006 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1847 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1849 (p : Pattern) (guard : d2007 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1848 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1850 (p : Pattern) (guard : d2008 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2007 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1849 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1851 (p : Pattern) (guard : d2009 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2004 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1846 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2008 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1850 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1852 (p : Pattern) (guard : d2010 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2009 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1851 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1853 (p : Pattern) (guard : d2011 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2010 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1852 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1854 (p : Pattern) (guard : d2012 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2011 p = 1 := by simpa only [d2012, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1853 p hg
    simpa only [d2012, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2012, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d2012, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1855 (p : Pattern) (guard : d2013 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1839 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1856 (p : Pattern) (guard : d2014 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1840 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1855 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1857 (p : Pattern) (guard : d2015 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1999 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1841 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1856 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1858 (p : Pattern) (guard : d2016 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d2016, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1225 p hg
    simpa only [d2016, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2016, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1154 p hg
    simpa only [d2016, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1859 (p : Pattern) (guard : d2017 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1839 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2016 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1858 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1860 (p : Pattern) (guard : d2018 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2017 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1859 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1861 (p : Pattern) (guard : d2019 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1844 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2018 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1860 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1862 (p : Pattern) (guard : d2020 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2015 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1857 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2019 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1861 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1863 (p : Pattern) (guard : d2021 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d2016 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1858 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1864 (p : Pattern) (guard : d2022 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2021 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1863 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1865 (p : Pattern) (guard : d2023 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1848 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2022 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1864 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1866 (p : Pattern) (guard : d2024 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2023 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1865 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1867 (p : Pattern) (guard : d2025 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2020 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1862 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2024 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1866 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1868 (p : Pattern) (guard : d2026 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2009 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1851 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2025 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1867 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1869 (p : Pattern) (guard : d2027 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1855 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1870 (p : Pattern) (guard : d2028 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1869 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1871 (p : Pattern) (guard : d2029 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1870 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1872 (p : Pattern) (guard : d2030 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1871 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1873 (p : Pattern) (guard : d2031 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1872 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1874 (p : Pattern) (guard : d2032 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2026 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1868 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1873 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1875 (p : Pattern) (guard : d2033 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2032 p = 1 := by simpa only [d2033, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1874 p hg
    simpa only [d2033, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2033, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d2033, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1876 (p : Pattern) (guard : d2034 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2012 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1854 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2033 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1875 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1877 (p : Pattern) (guard : d2035 p = 1) : d47797 p ≤ (-1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2034 p = 1 := by simpa only [d2035, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1876 p hg
    simpa only [d2035, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2035, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d2035, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1878 (p : Pattern) (guard : d2336 p = 1) : d47798 p ≤ (-1 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2335 p = 1 := by simpa only [d2336, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1838 p hg
    simpa only [d2336, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2035 p = 1 := by simpa only [d2336, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1877 p hg
    simpa only [d2336, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1879 (p : Pattern) (guard : d18318 p = 1) : d47799 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2336 p = 1 := by simpa only [d18318, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1878 p hg
    simpa only [d18318, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18318, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d18318, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1880 (p : Pattern) (guard : d18319 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d18318 p = 1 := by simpa only [d18319, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1879 p hg
    simpa only [d18319, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18319, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d18319, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1881 (p : Pattern) (guard : d2039 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1817 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1830 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1882 (p : Pattern) (guard : d2040 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2018 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1821 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1883 (p : Pattern) (guard : d2041 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2039 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1881 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1882 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1884 (p : Pattern) (guard : d2042 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2022 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1825 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1885 (p : Pattern) (guard : d2043 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2042 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1884 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1886 (p : Pattern) (guard : d2044 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2041 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1883 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1885 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1887 (p : Pattern) (guard : d2045 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1828 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2044 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1886 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1888 (p : Pattern) (guard : d2046 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2027 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1830 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1889 (p : Pattern) (guard : d2047 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2046 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1888 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1890 (p : Pattern) (guard : d2048 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2047 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1889 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1891 (p : Pattern) (guard : d2049 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1833 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1890 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1892 (p : Pattern) (guard : d2050 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2045 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1887 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1891 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1893 (p : Pattern) (guard : d2051 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2050 p = 1 := by simpa only [d2051, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1892 p hg
    simpa only [d2051, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2051, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d2051, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1894 (p : Pattern) (guard : d2052 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2033 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1836 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2051 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1893 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1895 (p : Pattern) (guard : d2340 p = 1) : d47652 p ≤ (-1 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2340, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d2340, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2052 p = 1 := by simpa only [d2340, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1894 p hg
    simpa only [d2340, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1896 (p : Pattern) (guard : d2039 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1856 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1869 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1897 (p : Pattern) (guard : d2040 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2018 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1860 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1898 (p : Pattern) (guard : d2041 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2039 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1896 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1897 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1899 (p : Pattern) (guard : d2042 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2022 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1864 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1900 (p : Pattern) (guard : d2043 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2042 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1899 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1901 (p : Pattern) (guard : d2044 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2041 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1898 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1900 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1902 (p : Pattern) (guard : d2045 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1867 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2044 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1901 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1903 (p : Pattern) (guard : d2046 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2027 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1869 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1904 (p : Pattern) (guard : d2047 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2046 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1903 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1905 (p : Pattern) (guard : d2048 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2047 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1904 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1906 (p : Pattern) (guard : d2049 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1872 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1905 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1907 (p : Pattern) (guard : d2050 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2045 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1902 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1906 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1908 (p : Pattern) (guard : d2051 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2050 p = 1 := by simpa only [d2051, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1907 p hg
    simpa only [d2051, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2051, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d2051, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1909 (p : Pattern) (guard : d2052 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2033 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1875 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2051 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1908 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1910 (p : Pattern) (guard : d2053 p = 1) : d47797 p ≤ (-1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2052 p = 1 := by simpa only [d2053, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1909 p hg
    simpa only [d2053, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2053, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d2053, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1911 (p : Pattern) (guard : d2341 p = 1) : d47798 p ≤ (-1 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2340 p = 1 := by simpa only [d2341, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1895 p hg
    simpa only [d2341, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2053 p = 1 := by simpa only [d2341, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1910 p hg
    simpa only [d2341, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1912 (p : Pattern) (guard : d18336 p = 1) : d47799 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2341 p = 1 := by simpa only [d18336, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1911 p hg
    simpa only [d18336, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18336, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d18336, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1913 (p : Pattern) (guard : d18337 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d18336 p = 1 := by simpa only [d18337, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1912 p hg
    simpa only [d18337, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18337, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d18337, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1914 (p : Pattern) (guard : d60853 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d18319 p = 1 := by simpa only [d60853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1880 p hg
    simpa only [d60853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18337 p = 1 := by simpa only [d60853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1913 p hg
    simpa only [d60853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1915 (p : Pattern) (guard : d2058 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1882 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1916 (p : Pattern) (guard : d2059 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2058 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1915 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1885 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1917 (p : Pattern) (guard : d2060 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1916 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1890 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1918 (p : Pattern) (guard : d2061 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2048 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1890 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1919 (p : Pattern) (guard : d2062 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2060 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1917 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1918 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1920 (p : Pattern) (guard : d2063 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2062 p = 1 := by simpa only [d2063, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1919 p hg
    simpa only [d2063, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2063, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d2063, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1921 (p : Pattern) (guard : d2064 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2051 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1893 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2063 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1920 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1922 (p : Pattern) (guard : d2346 p = 1) : d47652 p ≤ (-1 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2346, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d2346, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2064 p = 1 := by simpa only [d2346, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1921 p hg
    simpa only [d2346, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1923 (p : Pattern) (guard : d2058 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1897 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1924 (p : Pattern) (guard : d2059 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2058 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1923 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1900 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1925 (p : Pattern) (guard : d2060 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1924 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1905 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1926 (p : Pattern) (guard : d2061 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2048 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1905 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1927 (p : Pattern) (guard : d2062 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2060 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1925 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1926 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1928 (p : Pattern) (guard : d2063 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2062 p = 1 := by simpa only [d2063, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1927 p hg
    simpa only [d2063, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2063, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d2063, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1929 (p : Pattern) (guard : d2064 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2051 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1908 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2063 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1928 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1930 (p : Pattern) (guard : d2065 p = 1) : d47797 p ≤ (-1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2064 p = 1 := by simpa only [d2065, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1929 p hg
    simpa only [d2065, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2065, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d2065, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1931 (p : Pattern) (guard : d2347 p = 1) : d47798 p ≤ (-1 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2346 p = 1 := by simpa only [d2347, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1922 p hg
    simpa only [d2347, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2065 p = 1 := by simpa only [d2347, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1930 p hg
    simpa only [d2347, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1932 (p : Pattern) (guard : d18369 p = 1) : d47799 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2347 p = 1 := by simpa only [d18369, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1931 p hg
    simpa only [d18369, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18369, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d18369, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1933 (p : Pattern) (guard : d18370 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d18369 p = 1 := by simpa only [d18370, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1932 p hg
    simpa only [d18370, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18370, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d18370, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1934 (p : Pattern) (guard : d60855 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d18337 p = 1 := by simpa only [d60855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1913 p hg
    simpa only [d60855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18370 p = 1 := by simpa only [d60855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1933 p hg
    simpa only [d60855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1935 (p : Pattern) (guard : d60856 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d60853 p = 1 := by simpa only [d60856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1914 p hg
    simpa only [d60856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60855 p = 1 := by simpa only [d60856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1934 p hg
    simpa only [d60856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1936 (p : Pattern) (guard : d18371 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d18370 p = 1 := by simpa only [d18371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1933 p hg
    simpa only [d18371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1175 p hg
    simpa only [d18371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1937 (p : Pattern) (guard : d60860 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d60855 p = 1 := by simpa only [d60860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1934 p hg
    simpa only [d60860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18371 p = 1 := by simpa only [d60860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1936 p hg
    simpa only [d60860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1938 (p : Pattern) (guard : d60861 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60856 p = 1 := by simpa only [d60861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1935 p hg
    simpa only [d60861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60860 p = 1 := by simpa only [d60861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1937 p hg
    simpa only [d60861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1939 (p : Pattern) (guard : d60862 p = 1) : d47804 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60862, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1135 p hg
    simpa only [d60862, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60861 p = 1 := by simpa only [d60862, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1938 p hg
    simpa only [d60862, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1940 (p : Pattern) (guard : d60863 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60863, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1134 p hg
    simpa only [d60863, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60862 p = 1 := by simpa only [d60863, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1939 p hg
    simpa only [d60863, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1941 (p : Pattern) (guard : d2076 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1916 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1942 (p : Pattern) (guard : d2077 p = 1) : d47630 p ≤ (-1 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2076 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1941 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1140 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1943 (p : Pattern) (guard : d2078 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2077 p = 1 := by simpa only [d2078, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1942 p hg
    simpa only [d2078, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2078, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1148 p hg
    simpa only [d2078, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1944 (p : Pattern) (guard : d2079 p = 1) : d47652 p ≤ (-1 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2078 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1943 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1150 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1945 (p : Pattern) (guard : d2361 p = 1) : d47652 p ≤ (-1 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2361, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1136 p hg
    simpa only [d2361, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2079 p = 1 := by simpa only [d2361, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1944 p hg
    simpa only [d2361, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1946 (p : Pattern) (guard : d2076 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1924 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1947 (p : Pattern) (guard : d2077 p = 1) : d47617 p ≤ (-1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2076 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1946 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1156 p hg
    simpa only [d2077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1948 (p : Pattern) (guard : d2078 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2077 p = 1 := by simpa only [d2078, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1947 p hg
    simpa only [d2078, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2078, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1164 p hg
    simpa only [d2078, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1949 (p : Pattern) (guard : d2079 p = 1) : d47619 p ≤ (-1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2078 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1948 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1166 p hg
    simpa only [d2079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1950 (p : Pattern) (guard : d2080 p = 1) : d47797 p ≤ (-1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2079 p = 1 := by simpa only [d2080, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1949 p hg
    simpa only [d2080, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2080, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1168 p hg
    simpa only [d2080, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1951 (p : Pattern) (guard : d2362 p = 1) : d47798 p ≤ (-1 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2361 p = 1 := by simpa only [d2362, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1945 p hg
    simpa only [d2362, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2080 p = 1 := by simpa only [d2362, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1950 p hg
    simpa only [d2362, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1952 (p : Pattern) (guard : d60865 p = 1) : d47799 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2362 p = 1 := by simpa only [d60865, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1951 p hg
    simpa only [d60865, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60865, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1171 p hg
    simpa only [d60865, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1953 (p : Pattern) (guard : d60866 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d60865 p = 1 := by simpa only [d60866, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1952 p hg
    simpa only [d60866, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60866, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1173 p hg
    simpa only [d60866, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1954 (p : Pattern) (guard : d60867 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d60866 p = 1 := by simpa only [d60867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1953 p hg
    simpa only [d60867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1175 p hg
    simpa only [d60867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1955 (p : Pattern) (guard : d60868 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d18371 p = 1 := by simpa only [d60868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1936 p hg
    simpa only [d60868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60867 p = 1 := by simpa only [d60868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1954 p hg
    simpa only [d60868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1956 (p : Pattern) (guard : d60869 p = 1) : d47803 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60860 p = 1 := by simpa only [d60869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1937 p hg
    simpa only [d60869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60868 p = 1 := by simpa only [d60869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1955 p hg
    simpa only [d60869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1957 (p : Pattern) (guard : d60870 p = 1) : d47804 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60870, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1135 p hg
    simpa only [d60870, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60869 p = 1 := by simpa only [d60870, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1956 p hg
    simpa only [d60870, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1958 (p : Pattern) (guard : d60871 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60871, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1134 p hg
    simpa only [d60871, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60870 p = 1 := by simpa only [d60871, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1957 p hg
    simpa only [d60871, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1959 (p : Pattern) (guard : d60872 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60863 p = 1 := by simpa only [d60872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1940 p hg
    simpa only [d60872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60871 p = 1 := by simpa only [d60872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1958 p hg
    simpa only [d60872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1960 (p : Pattern) (guard : d60877 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60871 p = 1 := by simpa only [d60877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1958 p hg
    simpa only [d60877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d60877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1961 (p : Pattern) (guard : d60878 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60872 p = 1 := by simpa only [d60878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1959 p hg
    simpa only [d60878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60877 p = 1 := by simpa only [d60878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1960 p hg
    simpa only [d60878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1962 (p : Pattern) (guard : d60879 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60878 p = 1 := by simpa only [d60879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1961 p hg
    simpa only [d60879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d60879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1963 (p : Pattern) (guard : d60880 p = 1) : d47807 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60879 p = 1 := by simpa only [d60880, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1962 p hg
    simpa only [d60880, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60880, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1185 p hg
    simpa only [d60880, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1964 (p : Pattern) (guard : d60881 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60881, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d60881, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60880 p = 1 := by simpa only [d60881, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1963 p hg
    simpa only [d60881, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1965 (p : Pattern) (guard : d60886 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60877 p = 1 := by simpa only [d60886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1960 p hg
    simpa only [d60886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d60886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1966 (p : Pattern) (guard : d60887 p = 1) : d47805 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60886 p = 1 := by simpa only [d60887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1965 p hg
    simpa only [d60887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1181 p hg
    simpa only [d60887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1967 (p : Pattern) (guard : d60888 p = 1) : d47807 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60887 p = 1 := by simpa only [d60888, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1966 p hg
    simpa only [d60888, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60888, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1185 p hg
    simpa only [d60888, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1968 (p : Pattern) (guard : d60889 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60889, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d60889, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60888 p = 1 := by simpa only [d60889, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1967 p hg
    simpa only [d60889, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1969 (p : Pattern) (guard : d60890 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60881 p = 1 := by simpa only [d60890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1964 p hg
    simpa only [d60890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60889 p = 1 := by simpa only [d60890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1968 p hg
    simpa only [d60890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1970 (p : Pattern) (guard : d60891 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60890 p = 1 := by simpa only [d60891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1969 p hg
    simpa only [d60891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1971 (p : Pattern) (guard : d60892 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60891 p = 1 := by simpa only [d60892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1970 p hg
    simpa only [d60892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1972 (p : Pattern) (guard : d60893 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60892 p = 1 := by simpa only [d60893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1971 p hg
    simpa only [d60893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1973 (p : Pattern) (guard : d60903 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60889 p = 1 := by simpa only [d60903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1968 p hg
    simpa only [d60903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1974 (p : Pattern) (guard : d60904 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60903 p = 1 := by simpa only [d60904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1973 p hg
    simpa only [d60904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1975 (p : Pattern) (guard : d60905 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60904 p = 1 := by simpa only [d60905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1974 p hg
    simpa only [d60905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1976 (p : Pattern) (guard : d60906 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60905 p = 1 := by simpa only [d60906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1975 p hg
    simpa only [d60906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d60906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1977 (p : Pattern) (guard : d61188 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60893 p = 1 := by simpa only [d61188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1972 p hg
    simpa only [d61188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60906 p = 1 := by simpa only [d61188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1976 p hg
    simpa only [d61188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1978 (p : Pattern) (guard : d61189 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61188 p = 1 := by simpa only [d61189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1977 p hg
    simpa only [d61189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1979 (p : Pattern) (guard : d61190 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d61189 p = 1 := by simpa only [d61190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1978 p hg
    simpa only [d61190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1980 (p : Pattern) (guard : d61191 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61190 p = 1 := by simpa only [d61191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1979 p hg
    simpa only [d61191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1981 (p : Pattern) (guard : d61192 p = 1) : d47808 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1132 p hg
    simpa only [d61192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61191 p = 1 := by simpa only [d61192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1980 p hg
    simpa only [d61192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1982 (p : Pattern) (guard : d61193 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61193, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d61193, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61192 p = 1 := by simpa only [d61193, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1981 p hg
    simpa only [d61193, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1983 (p : Pattern) (guard : d61194 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61193 p = 1 := by simpa only [d61194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1982 p hg
    simpa only [d61194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1984 (p : Pattern) (guard : d61195 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d61194 p = 1 := by simpa only [d61195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1983 p hg
    simpa only [d61195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1985 (p : Pattern) (guard : d61196 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d61195 p = 1 := by simpa only [d61196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1984 p hg
    simpa only [d61196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1986 (p : Pattern) (guard : d61197 p = 1) : d47809 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d61196 p = 1 := by simpa only [d61197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1985 p hg
    simpa only [d61197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1130 p hg
    simpa only [d61197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1987 (p : Pattern) (guard : d61198 p = 1) : d47865 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d61197 p = 1 := by simpa only [d61198, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1986 p hg
    simpa only [d61198, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d61198, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1202 p hg
    simpa only [d61198, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1988 (p : Pattern) (guard : d61199 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61199, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1129 p hg
    simpa only [d61199, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61198 p = 1 := by simpa only [d61199, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1987 p hg
    simpa only [d61199, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1989 (p : Pattern) (guard : d61200 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61199 p = 1 := by simpa only [d61200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1988 p hg
    simpa only [d61200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1990 (p : Pattern) (guard : d61201 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61200 p = 1 := by simpa only [d61201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1989 p hg
    simpa only [d61201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1991 (p : Pattern) (guard : d61202 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61201 p = 1 := by simpa only [d61202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1990 p hg
    simpa only [d61202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1992 (p : Pattern) (guard : d61203 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61202 p = 1 := by simpa only [d61203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1991 p hg
    simpa only [d61203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1993 (p : Pattern) (guard : d61204 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61203 p = 1 := by simpa only [d61204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1992 p hg
    simpa only [d61204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1994 (p : Pattern) (guard : d61205 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61204 p = 1 := by simpa only [d61205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1993 p hg
    simpa only [d61205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1995 (p : Pattern) (guard : d61206 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61205 p = 1 := by simpa only [d61206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1994 p hg
    simpa only [d61206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1996 (p : Pattern) (guard : d61207 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61206 p = 1 := by simpa only [d61207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1995 p hg
    simpa only [d61207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1997 (p : Pattern) (guard : d61208 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61207 p = 1 := by simpa only [d61208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1996 p hg
    simpa only [d61208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1998 (p : Pattern) (guard : d61209 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1128 p hg
    simpa only [d61209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61208 p = 1 := by simpa only [d61209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1997 p hg
    simpa only [d61209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1999 (p : Pattern) (guard : d61210 p = 1) : d47866 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d61187 p = 1 := by simpa only [d61210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1799 p hg
    simpa only [d61210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d61209 p = 1 := by simpa only [d61210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1998 p hg
    simpa only [d61210, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
