/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions87
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub10560 (p : Pattern) : d1798 (change p 204 (some 182)) = d1797 p := by
  change d1797 (change p 204 (some 182)) = d1797 p
  exact sub10559 p
theorem sub10561 (p : Pattern) : d1799 (change p 204 (some 182)) = d1797 p := by
  change d1798 (change p 204 (some 182)) = d1797 p
  exact sub10560 p
theorem sub10562 (p : Pattern) : d1800 (change p 204 (some 182)) = d5878 p := by
  change (if p 163 then d1799 (change p 204 (some 182)) else d1790 (change p 204 (some 182))) = d5878 p
  rw [sub10561, sub10551]
  rfl
theorem sub10563 (p : Pattern) : d1801 (change p 204 (some 182)) = d5879 p := by
  change (if p 162 then d1800 (change p 204 (some 182)) else d1784 (change p 204 (some 182))) = d5879 p
  rw [sub10562, sub10545]
  rfl
theorem sub10564 (p : Pattern) : d356 (change p 204 (some 182)) = d356 p := by
  change (if p 246 then d12 (change p 204 (some 182)) else d23 (change p 204 (some 182))) = d356 p
  rw [sub10415, sub10443]
  rfl
theorem sub10565 (p : Pattern) : d1802 (change p 204 (some 182)) = d1802 p := by
  change (if p 225 then d356 (change p 204 (some 182)) else d24 (change p 204 (some 182))) = d1802 p
  rw [sub10564, sub10444]
  rfl
theorem sub10566 (p : Pattern) : d1803 (change p 204 (some 182)) = d1803 p := by
  change (if p 224 then d356 (change p 204 (some 182)) else d1802 (change p 204 (some 182))) = d1803 p
  rw [sub10564, sub10565]
  rfl
theorem sub10567 (p : Pattern) : d1804 (change p 204 (some 182)) = d1803 p := by
  change d1803 (change p 204 (some 182)) = d1803 p
  exact sub10566 p
theorem sub10568 (p : Pattern) : d1805 (change p 204 (some 182)) = d1803 p := by
  change d1804 (change p 204 (some 182)) = d1803 p
  exact sub10567 p
theorem sub10569 (p : Pattern) : d1806 (change p 204 (some 182)) = d5880 p := by
  change (if p 163 then d12 (change p 204 (some 182)) else d1805 (change p 204 (some 182))) = d5880 p
  rw [sub10415, sub10568]
  rfl
theorem sub10570 (p : Pattern) : d1807 (change p 204 (some 182)) = d5881 p := by
  change (if p 162 then d1806 (change p 204 (some 182)) else d1800 (change p 204 (some 182))) = d5881 p
  rw [sub10569, sub10562]
  rfl
theorem sub10571 (p : Pattern) : d1808 (change p 204 (some 182)) = d5882 p := by
  change (if p 161 then d1807 (change p 204 (some 182)) else d1801 (change p 204 (some 182))) = d5882 p
  rw [sub10570, sub10563]
  rfl
theorem sub10572 (p : Pattern) : d1809 (change p 204 (some 182)) = d1717 p := by
  change d1718 (change p 204 (some 182)) = d1717 p
  exact sub10467 p
theorem sub10573 (p : Pattern) : d1810 (change p 204 (some 182)) = d1724 p := by
  change d1725 (change p 204 (some 182)) = d1724 p
  exact sub10478 p
theorem sub10574 (p : Pattern) : d1811 (change p 204 (some 182)) = d5861 p := by
  change (if p 163 then d1810 (change p 204 (some 182)) else d1809 (change p 204 (some 182))) = d5861 p
  rw [sub10573, sub10572]
  rfl
theorem sub10575 (p : Pattern) : d1812 (change p 204 (some 182)) = d5863 p := by
  change (if p 162 then d1757 (change p 204 (some 182)) else d1811 (change p 204 (some 182))) = d5863 p
  rw [sub10515, sub10574]
  rfl
theorem sub10576 (p : Pattern) : d1813 (change p 204 (some 182)) = d5864 p := by
  change (if p 161 then d12 (change p 204 (some 182)) else d1812 (change p 204 (some 182))) = d5864 p
  rw [sub10415, sub10575]
  rfl
theorem sub10577 (p : Pattern) : d1814 (change p 204 (some 182)) = d5883 p := by
  change (if p 160 then d1813 (change p 204 (some 182)) else d1808 (change p 204 (some 182))) = d5883 p
  rw [sub10576, sub10571]
  rfl
theorem sub10578 (p : Pattern) : d1815 (change p 204 (some 182)) = d5884 p := by
  change (if p 163 then d1809 (change p 204 (some 182)) else d1783 (change p 204 (some 182))) = d5884 p
  rw [sub10572, sub10544]
  rfl
theorem sub10579 (p : Pattern) : d1816 (change p 204 (some 182)) = d5885 p := by
  change (if p 163 then d1805 (change p 204 (some 182)) else d1799 (change p 204 (some 182))) = d5885 p
  rw [sub10568, sub10561]
  rfl
theorem sub10580 (p : Pattern) : d1817 (change p 204 (some 182)) = d5886 p := by
  change (if p 162 then d1816 (change p 204 (some 182)) else d1815 (change p 204 (some 182))) = d5886 p
  rw [sub10579, sub10578]
  rfl
theorem sub10581 (p : Pattern) : d1818 (change p 204 (some 182)) = d5887 p := by
  change (if p 163 then d1754 (change p 204 (some 182)) else d1799 (change p 204 (some 182))) = d5887 p
  rw [sub10512, sub10561]
  rfl
theorem sub10582 (p : Pattern) : d1819 (change p 204 (some 182)) = d5888 p := by
  change (if p 162 then d1757 (change p 204 (some 182)) else d1818 (change p 204 (some 182))) = d5888 p
  rw [sub10515, sub10581]
  rfl
theorem sub10583 (p : Pattern) : d1820 (change p 204 (some 182)) = d5889 p := by
  change (if p 161 then d1819 (change p 204 (some 182)) else d1817 (change p 204 (some 182))) = d5889 p
  rw [sub10582, sub10580]
  rfl
theorem sub10584 (p : Pattern) : d1821 (change p 204 (some 182)) = d5872 p := by
  change (if p 163 then d12 (change p 204 (some 182)) else d1810 (change p 204 (some 182))) = d5872 p
  rw [sub10415, sub10573]
  rfl
theorem sub10585 (p : Pattern) : d1822 (change p 204 (some 182)) = d5873 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d1821 (change p 204 (some 182))) = d5873 p
  rw [sub10415, sub10584]
  rfl
theorem sub10586 (p : Pattern) : d1823 (change p 204 (some 182)) = d5874 p := by
  change (if p 161 then d12 (change p 204 (some 182)) else d1822 (change p 204 (some 182))) = d5874 p
  rw [sub10415, sub10585]
  rfl
theorem sub10587 (p : Pattern) : d1824 (change p 204 (some 182)) = d5890 p := by
  change (if p 160 then d1823 (change p 204 (some 182)) else d1820 (change p 204 (some 182))) = d5890 p
  rw [sub10586, sub10583]
  rfl
theorem sub10588 (p : Pattern) : d1825 (change p 204 (some 182)) = d5891 p := by
  change (if p 141 then d1824 (change p 204 (some 182)) else d1814 (change p 204 (some 182))) = d5891 p
  rw [sub10587, sub10577]
  rfl
theorem sub10589 (p : Pattern) : d1826 (change p 204 (some 182)) = d5892 p := by
  change (if p 138 then d1825 (change p 204 (some 182)) else d1768 (change p 204 (some 182))) = d5892 p
  rw [sub10588, sub10529]
  rfl
theorem sub10590 (p : Pattern) : d1827 (change p 204 (some 182)) = d5893 p := by
  change (if p 163 then d1756 (change p 204 (some 182)) else d1805 (change p 204 (some 182))) = d5893 p
  rw [sub10514, sub10568]
  rfl
theorem sub10591 (p : Pattern) : d1828 (change p 204 (some 182)) = d5894 p := by
  change (if p 162 then d1757 (change p 204 (some 182)) else d1827 (change p 204 (some 182))) = d5894 p
  rw [sub10515, sub10590]
  rfl
theorem sub10592 (p : Pattern) : d1829 (change p 204 (some 182)) = d5895 p := by
  change (if p 162 then d12 (change p 204 (some 182)) else d1757 (change p 204 (some 182))) = d5895 p
  rw [sub10415, sub10515]
  rfl
theorem sub10593 (p : Pattern) : d1830 (change p 204 (some 182)) = d5896 p := by
  change (if p 161 then d1829 (change p 204 (some 182)) else d1828 (change p 204 (some 182))) = d5896 p
  rw [sub10592, sub10591]
  rfl
theorem sub10594 (p : Pattern) : d1831 (change p 204 (some 182)) = d5897 p := by
  change (if p 161 then d12 (change p 204 (some 182)) else d1829 (change p 204 (some 182))) = d5897 p
  rw [sub10415, sub10592]
  rfl
theorem sub10595 (p : Pattern) : d1832 (change p 204 (some 182)) = d5898 p := by
  change (if p 160 then d1831 (change p 204 (some 182)) else d1830 (change p 204 (some 182))) = d5898 p
  rw [sub10594, sub10593]
  rfl
theorem sub10596 (p : Pattern) : d1833 (change p 204 (some 182)) = d5899 p := by
  change (if p 160 then d12 (change p 204 (some 182)) else d1831 (change p 204 (some 182))) = d5899 p
  rw [sub10415, sub10594]
  rfl
theorem sub10597 (p : Pattern) : d1834 (change p 204 (some 182)) = d5900 p := by
  change (if p 141 then d1833 (change p 204 (some 182)) else d1832 (change p 204 (some 182))) = d5900 p
  rw [sub10596, sub10595]
  rfl
theorem sub10598 (p : Pattern) : d1835 (change p 204 (some 182)) = d5901 p := by
  change (if p 138 then d1834 (change p 204 (some 182)) else d1825 (change p 204 (some 182))) = d5901 p
  rw [sub10597, sub10588]
  rfl
theorem sub10599 (p : Pattern) : d1836 (change p 204 (some 182)) = d5902 p := by
  change (if p 116 then d1835 (change p 204 (some 182)) else d1826 (change p 204 (some 182))) = d5902 p
  rw [sub10598, sub10589]
  rfl
theorem sub10600 (p : Pattern) : d1837 (change p 204 (some 182)) = d1686 p := by
  change (if p 163 then d1692 (change p 204 (some 182)) else d1690 (change p 204 (some 182))) = d1686 p
  rw [sub10428, sub10426]
  simp only [ite_self]
theorem sub10601 (p : Pattern) : d1838 (change p 204 (some 182)) = d5857 p := by
  change (if p 162 then d1699 (change p 204 (some 182)) else d1837 (change p 204 (some 182))) = d5857 p
  rw [sub10440, sub10600]
  rfl
theorem sub10602 (p : Pattern) : d1839 (change p 204 (some 182)) = d5860 p := by
  change (if p 161 then d1708 (change p 204 (some 182)) else d1838 (change p 204 (some 182))) = d5860 p
  rw [sub10454, sub10601]
  rfl
theorem sub10603 (p : Pattern) : d1840 (change p 204 (some 182)) = d5865 p := by
  change (if p 160 then d1738 (change p 204 (some 182)) else d1839 (change p 204 (some 182))) = d5865 p
  rw [sub10495, sub10602]
  rfl
theorem sub10604 (p : Pattern) : d1841 (change p 204 (some 182)) = d5866 p := by
  change (if p 163 then d1747 (change p 204 (some 182)) else d1692 (change p 204 (some 182))) = d5866 p
  rw [sub10503, sub10428]
  rfl
theorem sub10605 (p : Pattern) : d1842 (change p 204 (some 182)) = d5868 p := by
  change (if p 162 then d1749 (change p 204 (some 182)) else d1841 (change p 204 (some 182))) = d5868 p
  rw [sub10505, sub10604]
  rfl
theorem sub10606 (p : Pattern) : d1843 (change p 204 (some 182)) = d5871 p := by
  change (if p 161 then d1758 (change p 204 (some 182)) else d1842 (change p 204 (some 182))) = d5871 p
  rw [sub10516, sub10605]
  rfl
theorem sub10607 (p : Pattern) : d1844 (change p 204 (some 182)) = d5875 p := by
  change (if p 160 then d1766 (change p 204 (some 182)) else d1843 (change p 204 (some 182))) = d5875 p
  rw [sub10527, sub10606]
  rfl
theorem sub10608 (p : Pattern) : d1845 (change p 204 (some 182)) = d5876 p := by
  change (if p 141 then d1844 (change p 204 (some 182)) else d1840 (change p 204 (some 182))) = d5876 p
  rw [sub10607, sub10603]
  rfl
theorem sub10609 (p : Pattern) : d1846 (change p 204 (some 182)) = d5892 p := by
  change (if p 138 then d1825 (change p 204 (some 182)) else d1845 (change p 204 (some 182))) = d5892 p
  rw [sub10588, sub10608]
  rfl
theorem sub10610 (p : Pattern) : d1847 (change p 204 (some 182)) = d5903 p := by
  change (if p 138 then d12 (change p 204 (some 182)) else d1825 (change p 204 (some 182))) = d5903 p
  rw [sub10415, sub10588]
  rfl
theorem sub10611 (p : Pattern) : d1848 (change p 204 (some 182)) = d5904 p := by
  change (if p 116 then d1847 (change p 204 (some 182)) else d1846 (change p 204 (some 182))) = d5904 p
  rw [sub10610, sub10609]
  rfl
theorem sub10612 (p : Pattern) : d1849 (change p 204 (some 182)) = d5905 p := by
  change (if p 115 then d1848 (change p 204 (some 182)) else d1836 (change p 204 (some 182))) = d5905 p
  rw [sub10611, sub10599]
  rfl
theorem sub10613 (p : Pattern) : d1851 (change p 204 (some 182)) = d1686 p := by
  change d1687 (change p 204 (some 182)) = d1686 p
  exact sub10424 p
theorem sub10614 (p : Pattern) : d1852 (change p 204 (some 182)) = d1686 p := by
  change (if p 163 then d1692 (change p 204 (some 182)) else d1851 (change p 204 (some 182))) = d1686 p
  rw [sub10428, sub10613]
  simp only [ite_self]
theorem sub10615 (p : Pattern) : d1853 (change p 204 (some 182)) = d5857 p := by
  change (if p 162 then d1699 (change p 204 (some 182)) else d1852 (change p 204 (some 182))) = d5857 p
  rw [sub10440, sub10614]
  rfl
theorem sub10616 (p : Pattern) : d1854 (change p 204 (some 182)) = d5860 p := by
  change (if p 161 then d1708 (change p 204 (some 182)) else d1853 (change p 204 (some 182))) = d5860 p
  rw [sub10454, sub10615]
  rfl
theorem sub10617 (p : Pattern) : d1855 (change p 204 (some 182)) = d5865 p := by
  change (if p 160 then d1738 (change p 204 (some 182)) else d1854 (change p 204 (some 182))) = d5865 p
  rw [sub10495, sub10616]
  rfl
theorem sub10618 (p : Pattern) : d1856 (change p 204 (some 182)) = d5866 p := by
  change (if p 163 then d1747 (change p 204 (some 182)) else d1690 (change p 204 (some 182))) = d5866 p
  rw [sub10503, sub10426]
  rfl
theorem sub10619 (p : Pattern) : d1857 (change p 204 (some 182)) = d5868 p := by
  change (if p 162 then d1749 (change p 204 (some 182)) else d1856 (change p 204 (some 182))) = d5868 p
  rw [sub10505, sub10618]
  rfl
theorem sub10620 (p : Pattern) : d1858 (change p 204 (some 182)) = d5871 p := by
  change (if p 161 then d1758 (change p 204 (some 182)) else d1857 (change p 204 (some 182))) = d5871 p
  rw [sub10516, sub10619]
  rfl
theorem sub10621 (p : Pattern) : d1859 (change p 204 (some 182)) = d5875 p := by
  change (if p 160 then d1766 (change p 204 (some 182)) else d1858 (change p 204 (some 182))) = d5875 p
  rw [sub10527, sub10620]
  rfl
theorem sub10622 (p : Pattern) : d1860 (change p 204 (some 182)) = d5876 p := by
  change (if p 141 then d1859 (change p 204 (some 182)) else d1855 (change p 204 (some 182))) = d5876 p
  rw [sub10621, sub10617]
  rfl
theorem sub10623 (p : Pattern) : d1861 (change p 204 (some 182)) = d5892 p := by
  change (if p 138 then d1825 (change p 204 (some 182)) else d1860 (change p 204 (some 182))) = d5892 p
  rw [sub10588, sub10622]
  rfl
theorem sub10624 (p : Pattern) : d1862 (change p 204 (some 182)) = d5902 p := by
  change (if p 116 then d1835 (change p 204 (some 182)) else d1861 (change p 204 (some 182))) = d5902 p
  rw [sub10598, sub10623]
  rfl
theorem sub10625 (p : Pattern) : d1863 (change p 204 (some 182)) = d5857 p := by
  change (if p 162 then d1699 (change p 204 (some 182)) else d1692 (change p 204 (some 182))) = d5857 p
  rw [sub10440, sub10428]
  rfl
theorem sub10626 (p : Pattern) : d1864 (change p 204 (some 182)) = d5860 p := by
  change (if p 161 then d1708 (change p 204 (some 182)) else d1863 (change p 204 (some 182))) = d5860 p
  rw [sub10454, sub10625]
  rfl
theorem sub10627 (p : Pattern) : d1865 (change p 204 (some 182)) = d5865 p := by
  change (if p 160 then d1738 (change p 204 (some 182)) else d1864 (change p 204 (some 182))) = d5865 p
  rw [sub10495, sub10626]
  rfl
theorem sub10628 (p : Pattern) : d1866 (change p 204 (some 182)) = d5876 p := by
  change (if p 141 then d1844 (change p 204 (some 182)) else d1865 (change p 204 (some 182))) = d5876 p
  rw [sub10607, sub10627]
  rfl
theorem sub10629 (p : Pattern) : d1867 (change p 204 (some 182)) = d5892 p := by
  change (if p 138 then d1825 (change p 204 (some 182)) else d1866 (change p 204 (some 182))) = d5892 p
  rw [sub10588, sub10628]
  rfl
theorem sub10630 (p : Pattern) : d1868 (change p 204 (some 182)) = d5904 p := by
  change (if p 116 then d1847 (change p 204 (some 182)) else d1867 (change p 204 (some 182))) = d5904 p
  rw [sub10610, sub10629]
  rfl
theorem sub10631 (p : Pattern) : d1869 (change p 204 (some 182)) = d5905 p := by
  change (if p 115 then d1868 (change p 204 (some 182)) else d1862 (change p 204 (some 182))) = d5905 p
  rw [sub10630, sub10624]
  rfl
theorem sub10632 (p : Pattern) : d1870 (change p 204 (some 182)) = d5905 p := by
  change (if p 71 then d1869 (change p 204 (some 182)) else d1849 (change p 204 (some 182))) = d5905 p
  rw [sub10631, sub10612]
  simp only [ite_self]
theorem sub10633 (p : Pattern) : d1 (change p 204 (some 182)) = d1 p := by
  rfl
theorem sub10634 (p : Pattern) : d102 (change p 204 (some 182)) = d102 p := by
  change (if p 247 then d12 (change p 204 (some 182)) else d1 (change p 204 (some 182))) = d102 p
  rw [sub10415, sub10633]
  rfl
theorem sub10635 (p : Pattern) : d103 (change p 204 (some 182)) = d103 p := by
  change (if p 246 then d102 (change p 204 (some 182)) else d1 (change p 204 (some 182))) = d103 p
  rw [sub10634, sub10633]
  rfl
theorem sub10636 (p : Pattern) : d3 (change p 204 (some 182)) = d3 p := by
  rfl
theorem sub10637 (p : Pattern) : d1872 (change p 204 (some 182)) = d1872 p := by
  change (if p 247 then d3 (change p 204 (some 182)) else d1 (change p 204 (some 182))) = d1872 p
  rw [sub10636, sub10633]
  rfl
theorem sub10638 (p : Pattern) : d115 (change p 204 (some 182)) = d115 p := by
  change (if p 247 then d12 (change p 204 (some 182)) else d3 (change p 204 (some 182))) = d115 p
  rw [sub10415, sub10636]
  rfl
theorem sub10639 (p : Pattern) : d1873 (change p 204 (some 182)) = d1873 p := by
  change (if p 246 then d115 (change p 204 (some 182)) else d1872 (change p 204 (some 182))) = d1873 p
  rw [sub10638, sub10637]
  rfl
theorem sub10640 (p : Pattern) : d1874 (change p 204 (some 182)) = d1874 p := by
  change (if p 225 then d1873 (change p 204 (some 182)) else d103 (change p 204 (some 182))) = d1874 p
  rw [sub10639, sub10635]
  rfl
theorem sub10641 (p : Pattern) : d1875 (change p 204 (some 182)) = d1875 p := by
  change (if p 224 then d1873 (change p 204 (some 182)) else d1874 (change p 204 (some 182))) = d1875 p
  rw [sub10639, sub10640]
  rfl
theorem sub10642 (p : Pattern) : d1876 (change p 204 (some 182)) = d1875 p := by
  change d1875 (change p 204 (some 182)) = d1875 p
  exact sub10641 p
theorem sub10643 (p : Pattern) : d1877 (change p 204 (some 182)) = d1875 p := by
  change d1876 (change p 204 (some 182)) = d1875 p
  exact sub10642 p
theorem sub10644 (p : Pattern) : d1878 (change p 204 (some 182)) = d1875 p := by
  change d1876 (change p 204 (some 182)) = d1875 p
  exact sub10642 p
theorem sub10645 (p : Pattern) : d1879 (change p 204 (some 182)) = d1875 p := by
  change (if p 163 then d1878 (change p 204 (some 182)) else d1877 (change p 204 (some 182))) = d1875 p
  rw [sub10644, sub10643]
  simp only [ite_self]
theorem sub10646 (p : Pattern) : d5 (change p 204 (some 182)) = d5 p := by
  rfl
theorem sub10647 (p : Pattern) : d106 (change p 204 (some 182)) = d106 p := by
  change (if p 247 then d12 (change p 204 (some 182)) else d5 (change p 204 (some 182))) = d106 p
  rw [sub10415, sub10646]
  rfl
theorem sub10648 (p : Pattern) : d107 (change p 204 (some 182)) = d107 p := by
  change (if p 246 then d106 (change p 204 (some 182)) else d5 (change p 204 (some 182))) = d107 p
  rw [sub10647, sub10646]
  rfl
theorem sub10649 (p : Pattern) : d7 (change p 204 (some 182)) = d7 p := by
  rfl
theorem sub10650 (p : Pattern) : d1880 (change p 204 (some 182)) = d1880 p := by
  change (if p 247 then d7 (change p 204 (some 182)) else d5 (change p 204 (some 182))) = d1880 p
  rw [sub10649, sub10646]
  rfl
theorem sub10651 (p : Pattern) : d119 (change p 204 (some 182)) = d119 p := by
  change (if p 247 then d12 (change p 204 (some 182)) else d7 (change p 204 (some 182))) = d119 p
  rw [sub10415, sub10649]
  rfl
theorem sub10652 (p : Pattern) : d1881 (change p 204 (some 182)) = d1881 p := by
  change (if p 246 then d119 (change p 204 (some 182)) else d1880 (change p 204 (some 182))) = d1881 p
  rw [sub10651, sub10650]
  rfl
theorem sub10653 (p : Pattern) : d1882 (change p 204 (some 182)) = d1882 p := by
  change (if p 225 then d1881 (change p 204 (some 182)) else d107 (change p 204 (some 182))) = d1882 p
  rw [sub10652, sub10648]
  rfl
theorem sub10654 (p : Pattern) : d1883 (change p 204 (some 182)) = d1883 p := by
  change (if p 224 then d1881 (change p 204 (some 182)) else d1882 (change p 204 (some 182))) = d1883 p
  rw [sub10652, sub10653]
  rfl
theorem sub10655 (p : Pattern) : d1884 (change p 204 (some 182)) = d1883 p := by
  change d1883 (change p 204 (some 182)) = d1883 p
  exact sub10654 p
theorem sub10656 (p : Pattern) : d1885 (change p 204 (some 182)) = d1883 p := by
  change d1884 (change p 204 (some 182)) = d1883 p
  exact sub10655 p
theorem sub10657 (p : Pattern) : d1886 (change p 204 (some 182)) = d5906 p := by
  change (if p 163 then d1885 (change p 204 (some 182)) else d1878 (change p 204 (some 182))) = d5906 p
  rw [sub10656, sub10644]
  rfl
theorem sub10658 (p : Pattern) : d1887 (change p 204 (some 182)) = d5907 p := by
  change (if p 162 then d1886 (change p 204 (some 182)) else d1879 (change p 204 (some 182))) = d5907 p
  rw [sub10657, sub10645]
  rfl
theorem sub10659 (p : Pattern) : d1888 (change p 204 (some 182)) = d5908 p := by
  change (if p 163 then d12 (change p 204 (some 182)) else d1754 (change p 204 (some 182))) = d5908 p
  rw [sub10415, sub10512]
  rfl
theorem sub10660 (p : Pattern) : d1889 (change p 204 (some 182)) = d5909 p := by
  change (if p 162 then d1888 (change p 204 (some 182)) else d1886 (change p 204 (some 182))) = d5909 p
  rw [sub10659, sub10657]
  rfl
theorem sub10661 (p : Pattern) : d1890 (change p 204 (some 182)) = d5910 p := by
  change (if p 161 then d1889 (change p 204 (some 182)) else d1887 (change p 204 (some 182))) = d5910 p
  rw [sub10660, sub10658]
  rfl
theorem sub10662 (p : Pattern) : d116 (change p 204 (some 182)) = d116 p := by
  change (if p 246 then d115 (change p 204 (some 182)) else d3 (change p 204 (some 182))) = d116 p
  rw [sub10638, sub10636]
  rfl
theorem sub10663 (p : Pattern) : d1891 (change p 204 (some 182)) = d1891 p := by
  change (if p 247 then d9 (change p 204 (some 182)) else d3 (change p 204 (some 182))) = d1891 p
  rw [sub10442, sub10636]
  rfl
theorem sub10664 (p : Pattern) : d1892 (change p 204 (some 182)) = d1892 p := by
  change (if p 246 then d23 (change p 204 (some 182)) else d1891 (change p 204 (some 182))) = d1892 p
  rw [sub10443, sub10663]
  rfl
theorem sub10665 (p : Pattern) : d1893 (change p 204 (some 182)) = d1893 p := by
  change (if p 225 then d1892 (change p 204 (some 182)) else d116 (change p 204 (some 182))) = d1893 p
  rw [sub10664, sub10662]
  rfl
theorem sub10666 (p : Pattern) : d1894 (change p 204 (some 182)) = d1894 p := by
  change (if p 247 then d7 (change p 204 (some 182)) else d3 (change p 204 (some 182))) = d1894 p
  rw [sub10649, sub10636]
  rfl
theorem sub10667 (p : Pattern) : d1895 (change p 204 (some 182)) = d1895 p := by
  change (if p 246 then d119 (change p 204 (some 182)) else d1894 (change p 204 (some 182))) = d1895 p
  rw [sub10651, sub10666]
  rfl
theorem sub10668 (p : Pattern) : d1896 (change p 204 (some 182)) = d1896 p := by
  change (if p 246 then d12 (change p 204 (some 182)) else d115 (change p 204 (some 182))) = d1896 p
  rw [sub10415, sub10638]
  rfl
theorem sub10669 (p : Pattern) : d1897 (change p 204 (some 182)) = d1897 p := by
  change (if p 225 then d1896 (change p 204 (some 182)) else d1895 (change p 204 (some 182))) = d1897 p
  rw [sub10668, sub10667]
  rfl
theorem sub10670 (p : Pattern) : d1898 (change p 204 (some 182)) = d1898 p := by
  change (if p 224 then d1897 (change p 204 (some 182)) else d1893 (change p 204 (some 182))) = d1898 p
  rw [sub10669, sub10665]
  rfl
theorem sub10671 (p : Pattern) : d1899 (change p 204 (some 182)) = d1898 p := by
  change d1898 (change p 204 (some 182)) = d1898 p
  exact sub10670 p
theorem sub10672 (p : Pattern) : d1900 (change p 204 (some 182)) = d1898 p := by
  change d1899 (change p 204 (some 182)) = d1898 p
  exact sub10671 p
theorem sub10673 (p : Pattern) : d120 (change p 204 (some 182)) = d120 p := by
  change (if p 246 then d119 (change p 204 (some 182)) else d7 (change p 204 (some 182))) = d120 p
  rw [sub10651, sub10649]
  rfl
theorem sub10674 (p : Pattern) : d317 (change p 204 (some 182)) = d317 p := by
  change (if p 246 then d12 (change p 204 (some 182)) else d119 (change p 204 (some 182))) = d317 p
  rw [sub10415, sub10651]
  rfl
theorem sub10675 (p : Pattern) : d1901 (change p 204 (some 182)) = d1901 p := by
  change (if p 225 then d317 (change p 204 (some 182)) else d120 (change p 204 (some 182))) = d1901 p
  rw [sub10674, sub10673]
  rfl
theorem sub10676 (p : Pattern) : d1902 (change p 204 (some 182)) = d1902 p := by
  change (if p 247 then d11 (change p 204 (some 182)) else d7 (change p 204 (some 182))) = d1902 p
  rw [sub10445, sub10649]
  rfl
theorem sub10677 (p : Pattern) : d1903 (change p 204 (some 182)) = d1903 p := by
  change (if p 246 then d39 (change p 204 (some 182)) else d1902 (change p 204 (some 182))) = d1903 p
  rw [sub10447, sub10676]
  rfl
theorem sub10678 (p : Pattern) : d1904 (change p 204 (some 182)) = d1904 p := by
  change (if p 225 then d317 (change p 204 (some 182)) else d1903 (change p 204 (some 182))) = d1904 p
  rw [sub10674, sub10677]
  rfl
theorem sub10679 (p : Pattern) : d1905 (change p 204 (some 182)) = d1905 p := by
  change (if p 224 then d1904 (change p 204 (some 182)) else d1901 (change p 204 (some 182))) = d1905 p
  rw [sub10678, sub10675]
  rfl
end NetHack.Sokoban22Refined85
