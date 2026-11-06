/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Nodes14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d1800 (p : Pattern) : Int := if p 133 then d2 p else d1778 p
theorem agree1800 (p q : Pattern) (h : Agree support p q) : d1800 p = d1800 q := by
  simp only [d1800, h 133 (by decide), agree2 p q h, agree1778 p q h]
theorem nonnegative1800 (p : Pattern) : 0 ≤ d1800 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative1778 p)
def d1801 (p : Pattern) : Int := if p 132 then d1800 p else d1778 p
theorem agree1801 (p q : Pattern) (h : Agree support p q) : d1801 p = d1801 q := by
  simp only [d1801, h 132 (by decide), agree1800 p q h, agree1778 p q h]
theorem nonnegative1801 (p : Pattern) : 0 ≤ d1801 p :=
  nonnegative_ite (p 132) (nonnegative1800 p) (nonnegative1778 p)
def d1802 (p : Pattern) : Int := if p 113 then d1801 p else d1799 p
theorem agree1802 (p q : Pattern) (h : Agree support p q) : d1802 p = d1802 q := by
  simp only [d1802, h 113 (by decide), agree1801 p q h, agree1799 p q h]
theorem nonnegative1802 (p : Pattern) : 0 ≤ d1802 p :=
  nonnegative_ite (p 113) (nonnegative1801 p) (nonnegative1799 p)
def d1803 (p : Pattern) : Int := if p 112 then d1802 p else d1797 p
theorem agree1803 (p q : Pattern) (h : Agree support p q) : d1803 p = d1803 q := by
  simp only [d1803, h 112 (by decide), agree1802 p q h, agree1797 p q h]
theorem nonnegative1803 (p : Pattern) : 0 ≤ d1803 p :=
  nonnegative_ite (p 112) (nonnegative1802 p) (nonnegative1797 p)
def d1804 (p : Pattern) : Int := if p 106 then d1803 p else d1794 p
theorem agree1804 (p q : Pattern) (h : Agree support p q) : d1804 p = d1804 q := by
  simp only [d1804, h 106 (by decide), agree1803 p q h, agree1794 p q h]
theorem nonnegative1804 (p : Pattern) : 0 ≤ d1804 p :=
  nonnegative_ite (p 106) (nonnegative1803 p) (nonnegative1794 p)
def d1805 (p : Pattern) : Int := if p 86 then d1804 p else d1791 p
theorem agree1805 (p q : Pattern) (h : Agree support p q) : d1805 p = d1805 q := by
  simp only [d1805, h 86 (by decide), agree1804 p q h, agree1791 p q h]
theorem nonnegative1805 (p : Pattern) : 0 ≤ d1805 p :=
  nonnegative_ite (p 86) (nonnegative1804 p) (nonnegative1791 p)
def d1806 (p : Pattern) : Int := if p 112 then d1789 p else d1783 p
theorem agree1806 (p q : Pattern) (h : Agree support p q) : d1806 p = d1806 q := by
  simp only [d1806, h 112 (by decide), agree1789 p q h, agree1783 p q h]
theorem nonnegative1806 (p : Pattern) : 0 ≤ d1806 p :=
  nonnegative_ite (p 112) (nonnegative1789 p) (nonnegative1783 p)
def d1807 (p : Pattern) : Int := if p 106 then d1806 p else d1777 p
theorem agree1807 (p q : Pattern) (h : Agree support p q) : d1807 p = d1807 q := by
  simp only [d1807, h 106 (by decide), agree1806 p q h, agree1777 p q h]
theorem nonnegative1807 (p : Pattern) : 0 ≤ d1807 p :=
  nonnegative_ite (p 106) (nonnegative1806 p) (nonnegative1777 p)
def d1808 (p : Pattern) : Int := if p 113 then d1778 p else d1779 p
theorem agree1808 (p q : Pattern) (h : Agree support p q) : d1808 p = d1808 q := by
  simp only [d1808, h 113 (by decide), agree1778 p q h, agree1779 p q h]
theorem nonnegative1808 (p : Pattern) : 0 ≤ d1808 p :=
  nonnegative_ite (p 113) (nonnegative1778 p) (nonnegative1779 p)
def d1809 (p : Pattern) : Int := if p 112 then d1808 p else d1793 p
theorem agree1809 (p q : Pattern) (h : Agree support p q) : d1809 p = d1809 q := by
  simp only [d1809, h 112 (by decide), agree1808 p q h, agree1793 p q h]
theorem nonnegative1809 (p : Pattern) : 0 ≤ d1809 p :=
  nonnegative_ite (p 112) (nonnegative1808 p) (nonnegative1793 p)
def d1810 (p : Pattern) : Int := if p 113 then d1788 p else d1783 p
theorem agree1810 (p q : Pattern) (h : Agree support p q) : d1810 p = d1810 q := by
  simp only [d1810, h 113 (by decide), agree1788 p q h, agree1783 p q h]
theorem nonnegative1810 (p : Pattern) : 0 ≤ d1810 p :=
  nonnegative_ite (p 113) (nonnegative1788 p) (nonnegative1783 p)
def d1811 (p : Pattern) : Int := if p 113 then d2 p else d1801 p
theorem agree1811 (p q : Pattern) (h : Agree support p q) : d1811 p = d1811 q := by
  simp only [d1811, h 113 (by decide), agree2 p q h, agree1801 p q h]
theorem nonnegative1811 (p : Pattern) : 0 ≤ d1811 p :=
  nonnegative_ite (p 113) (nonnegative2 p) (nonnegative1801 p)
def d1812 (p : Pattern) : Int := if p 112 then d1811 p else d1810 p
theorem agree1812 (p q : Pattern) (h : Agree support p q) : d1812 p = d1812 q := by
  simp only [d1812, h 112 (by decide), agree1811 p q h, agree1810 p q h]
theorem nonnegative1812 (p : Pattern) : 0 ≤ d1812 p :=
  nonnegative_ite (p 112) (nonnegative1811 p) (nonnegative1810 p)
def d1813 (p : Pattern) : Int := if p 106 then d1812 p else d1809 p
theorem agree1813 (p q : Pattern) (h : Agree support p q) : d1813 p = d1813 q := by
  simp only [d1813, h 106 (by decide), agree1812 p q h, agree1809 p q h]
theorem nonnegative1813 (p : Pattern) : 0 ≤ d1813 p :=
  nonnegative_ite (p 106) (nonnegative1812 p) (nonnegative1809 p)
def d1814 (p : Pattern) : Int := if p 86 then d1813 p else d1807 p
theorem agree1814 (p q : Pattern) (h : Agree support p q) : d1814 p = d1814 q := by
  simp only [d1814, h 86 (by decide), agree1813 p q h, agree1807 p q h]
theorem nonnegative1814 (p : Pattern) : 0 ≤ d1814 p :=
  nonnegative_ite (p 86) (nonnegative1813 p) (nonnegative1807 p)
def d1815 (p : Pattern) : Int := if p 80 then d1814 p else d1805 p
theorem agree1815 (p q : Pattern) (h : Agree support p q) : d1815 p = d1815 q := by
  simp only [d1815, h 80 (by decide), agree1814 p q h, agree1805 p q h]
theorem nonnegative1815 (p : Pattern) : 0 ≤ d1815 p :=
  nonnegative_ite (p 80) (nonnegative1814 p) (nonnegative1805 p)
def d1816 (p : Pattern) : Int := if p 158 then d2 p else d0 p
theorem agree1816 (p q : Pattern) (h : Agree support p q) : d1816 p = d1816 q := by
  simp only [d1816, h 158 (by decide), agree2 p q h, agree0 p q h]
theorem nonnegative1816 (p : Pattern) : 0 ≤ d1816 p :=
  nonnegative_ite (p 158) (nonnegative2 p) (nonnegative0 p)
def d1817 (p : Pattern) : Int := if p 158 then d2 p else d1 p
theorem agree1817 (p q : Pattern) (h : Agree support p q) : d1817 p = d1817 q := by
  simp only [d1817, h 158 (by decide), agree2 p q h, agree1 p q h]
theorem nonnegative1817 (p : Pattern) : 0 ≤ d1817 p :=
  nonnegative_ite (p 158) (nonnegative2 p) (nonnegative1 p)
def d1818 (p : Pattern) : Int := if p 139 then d1817 p else d1816 p
theorem agree1818 (p q : Pattern) (h : Agree support p q) : d1818 p = d1818 q := by
  simp only [d1818, h 139 (by decide), agree1817 p q h, agree1816 p q h]
theorem nonnegative1818 (p : Pattern) : 0 ≤ d1818 p :=
  nonnegative_ite (p 139) (nonnegative1817 p) (nonnegative1816 p)
def d1819 (p : Pattern) : Int := if p 138 then d1818 p else d1816 p
theorem agree1819 (p q : Pattern) (h : Agree support p q) : d1819 p = d1819 q := by
  simp only [d1819, h 138 (by decide), agree1818 p q h, agree1816 p q h]
theorem nonnegative1819 (p : Pattern) : 0 ≤ d1819 p :=
  nonnegative_ite (p 138) (nonnegative1818 p) (nonnegative1816 p)
def d1820 (p : Pattern) : Int := if p 139 then d2 p else d1816 p
theorem agree1820 (p q : Pattern) (h : Agree support p q) : d1820 p = d1820 q := by
  simp only [d1820, h 139 (by decide), agree2 p q h, agree1816 p q h]
theorem nonnegative1820 (p : Pattern) : 0 ≤ d1820 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative1816 p)
def d1821 (p : Pattern) : Int := if p 138 then d1820 p else d1818 p
theorem agree1821 (p q : Pattern) (h : Agree support p q) : d1821 p = d1821 q := by
  simp only [d1821, h 138 (by decide), agree1820 p q h, agree1818 p q h]
theorem nonnegative1821 (p : Pattern) : 0 ≤ d1821 p :=
  nonnegative_ite (p 138) (nonnegative1820 p) (nonnegative1818 p)
def d1822 (p : Pattern) : Int := if p 113 then d1821 p else d1818 p
theorem agree1822 (p q : Pattern) (h : Agree support p q) : d1822 p = d1822 q := by
  simp only [d1822, h 113 (by decide), agree1821 p q h, agree1818 p q h]
theorem nonnegative1822 (p : Pattern) : 0 ≤ d1822 p :=
  nonnegative_ite (p 113) (nonnegative1821 p) (nonnegative1818 p)
def d1823 (p : Pattern) : Int := if p 112 then d1822 p else d1819 p
theorem agree1823 (p q : Pattern) (h : Agree support p q) : d1823 p = d1823 q := by
  simp only [d1823, h 112 (by decide), agree1822 p q h, agree1819 p q h]
theorem nonnegative1823 (p : Pattern) : 0 ≤ d1823 p :=
  nonnegative_ite (p 112) (nonnegative1822 p) (nonnegative1819 p)
def d1824 (p : Pattern) : Int := if p 139 then d2 p else d1817 p
theorem agree1824 (p q : Pattern) (h : Agree support p q) : d1824 p = d1824 q := by
  simp only [d1824, h 139 (by decide), agree2 p q h, agree1817 p q h]
theorem nonnegative1824 (p : Pattern) : 0 ≤ d1824 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative1817 p)
def d1825 (p : Pattern) : Int := if p 138 then d1824 p else d1817 p
theorem agree1825 (p q : Pattern) (h : Agree support p q) : d1825 p = d1825 q := by
  simp only [d1825, h 138 (by decide), agree1824 p q h, agree1817 p q h]
theorem nonnegative1825 (p : Pattern) : 0 ≤ d1825 p :=
  nonnegative_ite (p 138) (nonnegative1824 p) (nonnegative1817 p)
def d1826 (p : Pattern) : Int := if p 133 then d1825 p else d1819 p
theorem agree1826 (p q : Pattern) (h : Agree support p q) : d1826 p = d1826 q := by
  simp only [d1826, h 133 (by decide), agree1825 p q h, agree1819 p q h]
theorem nonnegative1826 (p : Pattern) : 0 ≤ d1826 p :=
  nonnegative_ite (p 133) (nonnegative1825 p) (nonnegative1819 p)
def d1827 (p : Pattern) : Int := if p 132 then d1826 p else d1819 p
theorem agree1827 (p q : Pattern) (h : Agree support p q) : d1827 p = d1827 q := by
  simp only [d1827, h 132 (by decide), agree1826 p q h, agree1819 p q h]
theorem nonnegative1827 (p : Pattern) : 0 ≤ d1827 p :=
  nonnegative_ite (p 132) (nonnegative1826 p) (nonnegative1819 p)
def d1828 (p : Pattern) : Int := if p 133 then d1824 p else d1819 p
theorem agree1828 (p q : Pattern) (h : Agree support p q) : d1828 p = d1828 q := by
  simp only [d1828, h 133 (by decide), agree1824 p q h, agree1819 p q h]
theorem nonnegative1828 (p : Pattern) : 0 ≤ d1828 p :=
  nonnegative_ite (p 133) (nonnegative1824 p) (nonnegative1819 p)
def d1829 (p : Pattern) : Int := if p 132 then d1828 p else d1819 p
theorem agree1829 (p q : Pattern) (h : Agree support p q) : d1829 p = d1829 q := by
  simp only [d1829, h 132 (by decide), agree1828 p q h, agree1819 p q h]
theorem nonnegative1829 (p : Pattern) : 0 ≤ d1829 p :=
  nonnegative_ite (p 132) (nonnegative1828 p) (nonnegative1819 p)
def d1830 (p : Pattern) : Int := if p 113 then d1829 p else d1827 p
theorem agree1830 (p q : Pattern) (h : Agree support p q) : d1830 p = d1830 q := by
  simp only [d1830, h 113 (by decide), agree1829 p q h, agree1827 p q h]
theorem nonnegative1830 (p : Pattern) : 0 ≤ d1830 p :=
  nonnegative_ite (p 113) (nonnegative1829 p) (nonnegative1827 p)
def d1831 (p : Pattern) : Int := if p 133 then d1824 p else d1818 p
theorem agree1831 (p q : Pattern) (h : Agree support p q) : d1831 p = d1831 q := by
  simp only [d1831, h 133 (by decide), agree1824 p q h, agree1818 p q h]
theorem nonnegative1831 (p : Pattern) : 0 ≤ d1831 p :=
  nonnegative_ite (p 133) (nonnegative1824 p) (nonnegative1818 p)
def d1832 (p : Pattern) : Int := if p 132 then d1831 p else d1818 p
theorem agree1832 (p q : Pattern) (h : Agree support p q) : d1832 p = d1832 q := by
  simp only [d1832, h 132 (by decide), agree1831 p q h, agree1818 p q h]
theorem nonnegative1832 (p : Pattern) : 0 ≤ d1832 p :=
  nonnegative_ite (p 132) (nonnegative1831 p) (nonnegative1818 p)
def d1833 (p : Pattern) : Int := if p 133 then d1824 p else d1821 p
theorem agree1833 (p q : Pattern) (h : Agree support p q) : d1833 p = d1833 q := by
  simp only [d1833, h 133 (by decide), agree1824 p q h, agree1821 p q h]
theorem nonnegative1833 (p : Pattern) : 0 ≤ d1833 p :=
  nonnegative_ite (p 133) (nonnegative1824 p) (nonnegative1821 p)
def d1834 (p : Pattern) : Int := if p 132 then d1833 p else d1821 p
theorem agree1834 (p q : Pattern) (h : Agree support p q) : d1834 p = d1834 q := by
  simp only [d1834, h 132 (by decide), agree1833 p q h, agree1821 p q h]
theorem nonnegative1834 (p : Pattern) : 0 ≤ d1834 p :=
  nonnegative_ite (p 132) (nonnegative1833 p) (nonnegative1821 p)
def d1835 (p : Pattern) : Int := if p 113 then d1834 p else d1832 p
theorem agree1835 (p q : Pattern) (h : Agree support p q) : d1835 p = d1835 q := by
  simp only [d1835, h 113 (by decide), agree1834 p q h, agree1832 p q h]
theorem nonnegative1835 (p : Pattern) : 0 ≤ d1835 p :=
  nonnegative_ite (p 113) (nonnegative1834 p) (nonnegative1832 p)
def d1836 (p : Pattern) : Int := if p 112 then d1835 p else d1830 p
theorem agree1836 (p q : Pattern) (h : Agree support p q) : d1836 p = d1836 q := by
  simp only [d1836, h 112 (by decide), agree1835 p q h, agree1830 p q h]
theorem nonnegative1836 (p : Pattern) : 0 ≤ d1836 p :=
  nonnegative_ite (p 112) (nonnegative1835 p) (nonnegative1830 p)
def d1837 (p : Pattern) : Int := if p 106 then d1836 p else d1823 p
theorem agree1837 (p q : Pattern) (h : Agree support p q) : d1837 p = d1837 q := by
  simp only [d1837, h 106 (by decide), agree1836 p q h, agree1823 p q h]
theorem nonnegative1837 (p : Pattern) : 0 ≤ d1837 p :=
  nonnegative_ite (p 106) (nonnegative1836 p) (nonnegative1823 p)
def d1838 (p : Pattern) : Int := if p 138 then d1820 p else d1816 p
theorem agree1838 (p q : Pattern) (h : Agree support p q) : d1838 p = d1838 q := by
  simp only [d1838, h 138 (by decide), agree1820 p q h, agree1816 p q h]
theorem nonnegative1838 (p : Pattern) : 0 ≤ d1838 p :=
  nonnegative_ite (p 138) (nonnegative1820 p) (nonnegative1816 p)
def d1839 (p : Pattern) : Int := if p 113 then d1838 p else d1819 p
theorem agree1839 (p q : Pattern) (h : Agree support p q) : d1839 p = d1839 q := by
  simp only [d1839, h 113 (by decide), agree1838 p q h, agree1819 p q h]
theorem nonnegative1839 (p : Pattern) : 0 ≤ d1839 p :=
  nonnegative_ite (p 113) (nonnegative1838 p) (nonnegative1819 p)
def d1840 (p : Pattern) : Int := if p 112 then d1825 p else d1839 p
theorem agree1840 (p q : Pattern) (h : Agree support p q) : d1840 p = d1840 q := by
  simp only [d1840, h 112 (by decide), agree1825 p q h, agree1839 p q h]
theorem nonnegative1840 (p : Pattern) : 0 ≤ d1840 p :=
  nonnegative_ite (p 112) (nonnegative1825 p) (nonnegative1839 p)
def d1841 (p : Pattern) : Int := if p 133 then d1824 p else d1838 p
theorem agree1841 (p q : Pattern) (h : Agree support p q) : d1841 p = d1841 q := by
  simp only [d1841, h 133 (by decide), agree1824 p q h, agree1838 p q h]
theorem nonnegative1841 (p : Pattern) : 0 ≤ d1841 p :=
  nonnegative_ite (p 133) (nonnegative1824 p) (nonnegative1838 p)
def d1842 (p : Pattern) : Int := if p 132 then d1841 p else d1838 p
theorem agree1842 (p q : Pattern) (h : Agree support p q) : d1842 p = d1842 q := by
  simp only [d1842, h 132 (by decide), agree1841 p q h, agree1838 p q h]
theorem nonnegative1842 (p : Pattern) : 0 ≤ d1842 p :=
  nonnegative_ite (p 132) (nonnegative1841 p) (nonnegative1838 p)
def d1843 (p : Pattern) : Int := if p 113 then d1842 p else d1829 p
theorem agree1843 (p q : Pattern) (h : Agree support p q) : d1843 p = d1843 q := by
  simp only [d1843, h 113 (by decide), agree1842 p q h, agree1829 p q h]
theorem nonnegative1843 (p : Pattern) : 0 ≤ d1843 p :=
  nonnegative_ite (p 113) (nonnegative1842 p) (nonnegative1829 p)
def d1844 (p : Pattern) : Int := if p 133 then d2 p else d1825 p
theorem agree1844 (p q : Pattern) (h : Agree support p q) : d1844 p = d1844 q := by
  simp only [d1844, h 133 (by decide), agree2 p q h, agree1825 p q h]
theorem nonnegative1844 (p : Pattern) : 0 ≤ d1844 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative1825 p)
def d1845 (p : Pattern) : Int := if p 132 then d1844 p else d1825 p
theorem agree1845 (p q : Pattern) (h : Agree support p q) : d1845 p = d1845 q := by
  simp only [d1845, h 132 (by decide), agree1844 p q h, agree1825 p q h]
theorem nonnegative1845 (p : Pattern) : 0 ≤ d1845 p :=
  nonnegative_ite (p 132) (nonnegative1844 p) (nonnegative1825 p)
def d1846 (p : Pattern) : Int := if p 133 then d2 p else d1824 p
theorem agree1846 (p q : Pattern) (h : Agree support p q) : d1846 p = d1846 q := by
  simp only [d1846, h 133 (by decide), agree2 p q h, agree1824 p q h]
theorem nonnegative1846 (p : Pattern) : 0 ≤ d1846 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative1824 p)
def d1847 (p : Pattern) : Int := if p 132 then d1846 p else d1824 p
theorem agree1847 (p q : Pattern) (h : Agree support p q) : d1847 p = d1847 q := by
  simp only [d1847, h 132 (by decide), agree1846 p q h, agree1824 p q h]
theorem nonnegative1847 (p : Pattern) : 0 ≤ d1847 p :=
  nonnegative_ite (p 132) (nonnegative1846 p) (nonnegative1824 p)
def d1848 (p : Pattern) : Int := if p 113 then d1847 p else d1845 p
theorem agree1848 (p q : Pattern) (h : Agree support p q) : d1848 p = d1848 q := by
  simp only [d1848, h 113 (by decide), agree1847 p q h, agree1845 p q h]
theorem nonnegative1848 (p : Pattern) : 0 ≤ d1848 p :=
  nonnegative_ite (p 113) (nonnegative1847 p) (nonnegative1845 p)
def d1849 (p : Pattern) : Int := if p 112 then d1848 p else d1843 p
theorem agree1849 (p q : Pattern) (h : Agree support p q) : d1849 p = d1849 q := by
  simp only [d1849, h 112 (by decide), agree1848 p q h, agree1843 p q h]
theorem nonnegative1849 (p : Pattern) : 0 ≤ d1849 p :=
  nonnegative_ite (p 112) (nonnegative1848 p) (nonnegative1843 p)
def d1850 (p : Pattern) : Int := if p 106 then d1849 p else d1840 p
theorem agree1850 (p q : Pattern) (h : Agree support p q) : d1850 p = d1850 q := by
  simp only [d1850, h 106 (by decide), agree1849 p q h, agree1840 p q h]
theorem nonnegative1850 (p : Pattern) : 0 ≤ d1850 p :=
  nonnegative_ite (p 106) (nonnegative1849 p) (nonnegative1840 p)
def d1851 (p : Pattern) : Int := if p 86 then d1850 p else d1837 p
theorem agree1851 (p q : Pattern) (h : Agree support p q) : d1851 p = d1851 q := by
  simp only [d1851, h 86 (by decide), agree1850 p q h, agree1837 p q h]
theorem nonnegative1851 (p : Pattern) : 0 ≤ d1851 p :=
  nonnegative_ite (p 86) (nonnegative1850 p) (nonnegative1837 p)
def d1852 (p : Pattern) : Int := if p 112 then d1835 p else d1829 p
theorem agree1852 (p q : Pattern) (h : Agree support p q) : d1852 p = d1852 q := by
  simp only [d1852, h 112 (by decide), agree1835 p q h, agree1829 p q h]
theorem nonnegative1852 (p : Pattern) : 0 ≤ d1852 p :=
  nonnegative_ite (p 112) (nonnegative1835 p) (nonnegative1829 p)
def d1853 (p : Pattern) : Int := if p 106 then d1852 p else d1823 p
theorem agree1853 (p q : Pattern) (h : Agree support p q) : d1853 p = d1853 q := by
  simp only [d1853, h 106 (by decide), agree1852 p q h, agree1823 p q h]
theorem nonnegative1853 (p : Pattern) : 0 ≤ d1853 p :=
  nonnegative_ite (p 106) (nonnegative1852 p) (nonnegative1823 p)
def d1854 (p : Pattern) : Int := if p 113 then d1824 p else d1825 p
theorem agree1854 (p q : Pattern) (h : Agree support p q) : d1854 p = d1854 q := by
  simp only [d1854, h 113 (by decide), agree1824 p q h, agree1825 p q h]
theorem nonnegative1854 (p : Pattern) : 0 ≤ d1854 p :=
  nonnegative_ite (p 113) (nonnegative1824 p) (nonnegative1825 p)
def d1855 (p : Pattern) : Int := if p 112 then d1854 p else d1839 p
theorem agree1855 (p q : Pattern) (h : Agree support p q) : d1855 p = d1855 q := by
  simp only [d1855, h 112 (by decide), agree1854 p q h, agree1839 p q h]
theorem nonnegative1855 (p : Pattern) : 0 ≤ d1855 p :=
  nonnegative_ite (p 112) (nonnegative1854 p) (nonnegative1839 p)
def d1856 (p : Pattern) : Int := if p 113 then d1834 p else d1829 p
theorem agree1856 (p q : Pattern) (h : Agree support p q) : d1856 p = d1856 q := by
  simp only [d1856, h 113 (by decide), agree1834 p q h, agree1829 p q h]
theorem nonnegative1856 (p : Pattern) : 0 ≤ d1856 p :=
  nonnegative_ite (p 113) (nonnegative1834 p) (nonnegative1829 p)
def d1857 (p : Pattern) : Int := if p 113 then d2 p else d1847 p
theorem agree1857 (p q : Pattern) (h : Agree support p q) : d1857 p = d1857 q := by
  simp only [d1857, h 113 (by decide), agree2 p q h, agree1847 p q h]
theorem nonnegative1857 (p : Pattern) : 0 ≤ d1857 p :=
  nonnegative_ite (p 113) (nonnegative2 p) (nonnegative1847 p)
def d1858 (p : Pattern) : Int := if p 112 then d1857 p else d1856 p
theorem agree1858 (p q : Pattern) (h : Agree support p q) : d1858 p = d1858 q := by
  simp only [d1858, h 112 (by decide), agree1857 p q h, agree1856 p q h]
theorem nonnegative1858 (p : Pattern) : 0 ≤ d1858 p :=
  nonnegative_ite (p 112) (nonnegative1857 p) (nonnegative1856 p)
def d1859 (p : Pattern) : Int := if p 106 then d1858 p else d1855 p
theorem agree1859 (p q : Pattern) (h : Agree support p q) : d1859 p = d1859 q := by
  simp only [d1859, h 106 (by decide), agree1858 p q h, agree1855 p q h]
theorem nonnegative1859 (p : Pattern) : 0 ≤ d1859 p :=
  nonnegative_ite (p 106) (nonnegative1858 p) (nonnegative1855 p)
def d1860 (p : Pattern) : Int := if p 86 then d1859 p else d1853 p
theorem agree1860 (p q : Pattern) (h : Agree support p q) : d1860 p = d1860 q := by
  simp only [d1860, h 86 (by decide), agree1859 p q h, agree1853 p q h]
theorem nonnegative1860 (p : Pattern) : 0 ≤ d1860 p :=
  nonnegative_ite (p 86) (nonnegative1859 p) (nonnegative1853 p)
def d1861 (p : Pattern) : Int := if p 80 then d1860 p else d1851 p
theorem agree1861 (p q : Pattern) (h : Agree support p q) : d1861 p = d1861 q := by
  simp only [d1861, h 80 (by decide), agree1860 p q h, agree1851 p q h]
theorem nonnegative1861 (p : Pattern) : 0 ≤ d1861 p :=
  nonnegative_ite (p 80) (nonnegative1860 p) (nonnegative1851 p)
def d1862 (p : Pattern) : Int := if p 139 then d1556 p else d1554 p
theorem agree1862 (p q : Pattern) (h : Agree support p q) : d1862 p = d1862 q := by
  simp only [d1862, h 139 (by decide), agree1556 p q h, agree1554 p q h]
theorem nonnegative1862 (p : Pattern) : 0 ≤ d1862 p :=
  nonnegative_ite (p 139) (nonnegative1556 p) (nonnegative1554 p)
def d1863 (p : Pattern) : Int := if p 138 then d1862 p else d1554 p
theorem agree1863 (p q : Pattern) (h : Agree support p q) : d1863 p = d1863 q := by
  simp only [d1863, h 138 (by decide), agree1862 p q h, agree1554 p q h]
theorem nonnegative1863 (p : Pattern) : 0 ≤ d1863 p :=
  nonnegative_ite (p 138) (nonnegative1862 p) (nonnegative1554 p)
def d1864 (p : Pattern) : Int := if p 158 then d2 p else d1554 p
theorem agree1864 (p q : Pattern) (h : Agree support p q) : d1864 p = d1864 q := by
  simp only [d1864, h 158 (by decide), agree2 p q h, agree1554 p q h]
theorem nonnegative1864 (p : Pattern) : 0 ≤ d1864 p :=
  nonnegative_ite (p 158) (nonnegative2 p) (nonnegative1554 p)
def d1865 (p : Pattern) : Int := if p 158 then d2 p else d1556 p
theorem agree1865 (p q : Pattern) (h : Agree support p q) : d1865 p = d1865 q := by
  simp only [d1865, h 158 (by decide), agree2 p q h, agree1556 p q h]
theorem nonnegative1865 (p : Pattern) : 0 ≤ d1865 p :=
  nonnegative_ite (p 158) (nonnegative2 p) (nonnegative1556 p)
def d1866 (p : Pattern) : Int := if p 139 then d1865 p else d1864 p
theorem agree1866 (p q : Pattern) (h : Agree support p q) : d1866 p = d1866 q := by
  simp only [d1866, h 139 (by decide), agree1865 p q h, agree1864 p q h]
theorem nonnegative1866 (p : Pattern) : 0 ≤ d1866 p :=
  nonnegative_ite (p 139) (nonnegative1865 p) (nonnegative1864 p)
def d1867 (p : Pattern) : Int := if p 138 then d1866 p else d1864 p
theorem agree1867 (p q : Pattern) (h : Agree support p q) : d1867 p = d1867 q := by
  simp only [d1867, h 138 (by decide), agree1866 p q h, agree1864 p q h]
theorem nonnegative1867 (p : Pattern) : 0 ≤ d1867 p :=
  nonnegative_ite (p 138) (nonnegative1866 p) (nonnegative1864 p)
def d1868 (p : Pattern) : Int := if p 134 then d1867 p else d1863 p
theorem agree1868 (p q : Pattern) (h : Agree support p q) : d1868 p = d1868 q := by
  simp only [d1868, h 134 (by decide), agree1867 p q h, agree1863 p q h]
theorem nonnegative1868 (p : Pattern) : 0 ≤ d1868 p :=
  nonnegative_ite (p 134) (nonnegative1867 p) (nonnegative1863 p)
def d1869 (p : Pattern) : Int := if p 133 then d1868 p else d1863 p
theorem agree1869 (p q : Pattern) (h : Agree support p q) : d1869 p = d1869 q := by
  simp only [d1869, h 133 (by decide), agree1868 p q h, agree1863 p q h]
theorem nonnegative1869 (p : Pattern) : 0 ≤ d1869 p :=
  nonnegative_ite (p 133) (nonnegative1868 p) (nonnegative1863 p)
def d1870 (p : Pattern) : Int := if p 133 then d1867 p else d1868 p
theorem agree1870 (p q : Pattern) (h : Agree support p q) : d1870 p = d1870 q := by
  simp only [d1870, h 133 (by decide), agree1867 p q h, agree1868 p q h]
theorem nonnegative1870 (p : Pattern) : 0 ≤ d1870 p :=
  nonnegative_ite (p 133) (nonnegative1867 p) (nonnegative1868 p)
def d1871 (p : Pattern) : Int := if p 132 then d1870 p else d1869 p
theorem agree1871 (p q : Pattern) (h : Agree support p q) : d1871 p = d1871 q := by
  simp only [d1871, h 132 (by decide), agree1870 p q h, agree1869 p q h]
theorem nonnegative1871 (p : Pattern) : 0 ≤ d1871 p :=
  nonnegative_ite (p 132) (nonnegative1870 p) (nonnegative1869 p)
def d1872 (p : Pattern) : Int := if p 134 then d1866 p else d1862 p
theorem agree1872 (p q : Pattern) (h : Agree support p q) : d1872 p = d1872 q := by
  simp only [d1872, h 134 (by decide), agree1866 p q h, agree1862 p q h]
theorem nonnegative1872 (p : Pattern) : 0 ≤ d1872 p :=
  nonnegative_ite (p 134) (nonnegative1866 p) (nonnegative1862 p)
def d1873 (p : Pattern) : Int := if p 133 then d1872 p else d1862 p
theorem agree1873 (p q : Pattern) (h : Agree support p q) : d1873 p = d1873 q := by
  simp only [d1873, h 133 (by decide), agree1872 p q h, agree1862 p q h]
theorem nonnegative1873 (p : Pattern) : 0 ≤ d1873 p :=
  nonnegative_ite (p 133) (nonnegative1872 p) (nonnegative1862 p)
def d1874 (p : Pattern) : Int := if p 133 then d1866 p else d1872 p
theorem agree1874 (p q : Pattern) (h : Agree support p q) : d1874 p = d1874 q := by
  simp only [d1874, h 133 (by decide), agree1866 p q h, agree1872 p q h]
theorem nonnegative1874 (p : Pattern) : 0 ≤ d1874 p :=
  nonnegative_ite (p 133) (nonnegative1866 p) (nonnegative1872 p)
def d1875 (p : Pattern) : Int := if p 132 then d1874 p else d1873 p
theorem agree1875 (p q : Pattern) (h : Agree support p q) : d1875 p = d1875 q := by
  simp only [d1875, h 132 (by decide), agree1874 p q h, agree1873 p q h]
theorem nonnegative1875 (p : Pattern) : 0 ≤ d1875 p :=
  nonnegative_ite (p 132) (nonnegative1874 p) (nonnegative1873 p)
def d1876 (p : Pattern) : Int := if p 139 then d2 p else d1554 p
theorem agree1876 (p q : Pattern) (h : Agree support p q) : d1876 p = d1876 q := by
  simp only [d1876, h 139 (by decide), agree2 p q h, agree1554 p q h]
theorem nonnegative1876 (p : Pattern) : 0 ≤ d1876 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative1554 p)
def d1877 (p : Pattern) : Int := if p 138 then d1876 p else d1862 p
theorem agree1877 (p q : Pattern) (h : Agree support p q) : d1877 p = d1877 q := by
  simp only [d1877, h 138 (by decide), agree1876 p q h, agree1862 p q h]
theorem nonnegative1877 (p : Pattern) : 0 ≤ d1877 p :=
  nonnegative_ite (p 138) (nonnegative1876 p) (nonnegative1862 p)
def d1878 (p : Pattern) : Int := if p 139 then d2 p else d1864 p
theorem agree1878 (p q : Pattern) (h : Agree support p q) : d1878 p = d1878 q := by
  simp only [d1878, h 139 (by decide), agree2 p q h, agree1864 p q h]
theorem nonnegative1878 (p : Pattern) : 0 ≤ d1878 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative1864 p)
def d1879 (p : Pattern) : Int := if p 138 then d1878 p else d1866 p
theorem agree1879 (p q : Pattern) (h : Agree support p q) : d1879 p = d1879 q := by
  simp only [d1879, h 138 (by decide), agree1878 p q h, agree1866 p q h]
theorem nonnegative1879 (p : Pattern) : 0 ≤ d1879 p :=
  nonnegative_ite (p 138) (nonnegative1878 p) (nonnegative1866 p)
def d1880 (p : Pattern) : Int := if p 134 then d1879 p else d1877 p
theorem agree1880 (p q : Pattern) (h : Agree support p q) : d1880 p = d1880 q := by
  simp only [d1880, h 134 (by decide), agree1879 p q h, agree1877 p q h]
theorem nonnegative1880 (p : Pattern) : 0 ≤ d1880 p :=
  nonnegative_ite (p 134) (nonnegative1879 p) (nonnegative1877 p)
def d1881 (p : Pattern) : Int := if p 133 then d1880 p else d1877 p
theorem agree1881 (p q : Pattern) (h : Agree support p q) : d1881 p = d1881 q := by
  simp only [d1881, h 133 (by decide), agree1880 p q h, agree1877 p q h]
theorem nonnegative1881 (p : Pattern) : 0 ≤ d1881 p :=
  nonnegative_ite (p 133) (nonnegative1880 p) (nonnegative1877 p)
def d1882 (p : Pattern) : Int := if p 133 then d1879 p else d1880 p
theorem agree1882 (p q : Pattern) (h : Agree support p q) : d1882 p = d1882 q := by
  simp only [d1882, h 133 (by decide), agree1879 p q h, agree1880 p q h]
theorem nonnegative1882 (p : Pattern) : 0 ≤ d1882 p :=
  nonnegative_ite (p 133) (nonnegative1879 p) (nonnegative1880 p)
def d1883 (p : Pattern) : Int := if p 132 then d1882 p else d1881 p
theorem agree1883 (p q : Pattern) (h : Agree support p q) : d1883 p = d1883 q := by
  simp only [d1883, h 132 (by decide), agree1882 p q h, agree1881 p q h]
theorem nonnegative1883 (p : Pattern) : 0 ≤ d1883 p :=
  nonnegative_ite (p 132) (nonnegative1882 p) (nonnegative1881 p)
def d1884 (p : Pattern) : Int := if p 113 then d1883 p else d1875 p
theorem agree1884 (p q : Pattern) (h : Agree support p q) : d1884 p = d1884 q := by
  simp only [d1884, h 113 (by decide), agree1883 p q h, agree1875 p q h]
theorem nonnegative1884 (p : Pattern) : 0 ≤ d1884 p :=
  nonnegative_ite (p 113) (nonnegative1883 p) (nonnegative1875 p)
def d1885 (p : Pattern) : Int := if p 112 then d1884 p else d1871 p
theorem agree1885 (p q : Pattern) (h : Agree support p q) : d1885 p = d1885 q := by
  simp only [d1885, h 112 (by decide), agree1884 p q h, agree1871 p q h]
theorem nonnegative1885 (p : Pattern) : 0 ≤ d1885 p :=
  nonnegative_ite (p 112) (nonnegative1884 p) (nonnegative1871 p)
def d1886 (p : Pattern) : Int := if p 139 then d2 p else d1865 p
theorem agree1886 (p q : Pattern) (h : Agree support p q) : d1886 p = d1886 q := by
  simp only [d1886, h 139 (by decide), agree2 p q h, agree1865 p q h]
theorem nonnegative1886 (p : Pattern) : 0 ≤ d1886 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative1865 p)
def d1887 (p : Pattern) : Int := if p 138 then d1886 p else d1865 p
theorem agree1887 (p q : Pattern) (h : Agree support p q) : d1887 p = d1887 q := by
  simp only [d1887, h 138 (by decide), agree1886 p q h, agree1865 p q h]
theorem nonnegative1887 (p : Pattern) : 0 ≤ d1887 p :=
  nonnegative_ite (p 138) (nonnegative1886 p) (nonnegative1865 p)
def d1888 (p : Pattern) : Int := if p 133 then d1887 p else d1868 p
theorem agree1888 (p q : Pattern) (h : Agree support p q) : d1888 p = d1888 q := by
  simp only [d1888, h 133 (by decide), agree1887 p q h, agree1868 p q h]
theorem nonnegative1888 (p : Pattern) : 0 ≤ d1888 p :=
  nonnegative_ite (p 133) (nonnegative1887 p) (nonnegative1868 p)
def d1889 (p : Pattern) : Int := if p 132 then d1888 p else d1869 p
theorem agree1889 (p q : Pattern) (h : Agree support p q) : d1889 p = d1889 q := by
  simp only [d1889, h 132 (by decide), agree1888 p q h, agree1869 p q h]
theorem nonnegative1889 (p : Pattern) : 0 ≤ d1889 p :=
  nonnegative_ite (p 132) (nonnegative1888 p) (nonnegative1869 p)
def d1890 (p : Pattern) : Int := if p 133 then d1886 p else d1868 p
theorem agree1890 (p q : Pattern) (h : Agree support p q) : d1890 p = d1890 q := by
  simp only [d1890, h 133 (by decide), agree1886 p q h, agree1868 p q h]
theorem nonnegative1890 (p : Pattern) : 0 ≤ d1890 p :=
  nonnegative_ite (p 133) (nonnegative1886 p) (nonnegative1868 p)
def d1891 (p : Pattern) : Int := if p 132 then d1890 p else d1869 p
theorem agree1891 (p q : Pattern) (h : Agree support p q) : d1891 p = d1891 q := by
  simp only [d1891, h 132 (by decide), agree1890 p q h, agree1869 p q h]
theorem nonnegative1891 (p : Pattern) : 0 ≤ d1891 p :=
  nonnegative_ite (p 132) (nonnegative1890 p) (nonnegative1869 p)
def d1892 (p : Pattern) : Int := if p 113 then d1891 p else d1889 p
theorem agree1892 (p q : Pattern) (h : Agree support p q) : d1892 p = d1892 q := by
  simp only [d1892, h 113 (by decide), agree1891 p q h, agree1889 p q h]
theorem nonnegative1892 (p : Pattern) : 0 ≤ d1892 p :=
  nonnegative_ite (p 113) (nonnegative1891 p) (nonnegative1889 p)
def d1893 (p : Pattern) : Int := if p 133 then d1886 p else d1872 p
theorem agree1893 (p q : Pattern) (h : Agree support p q) : d1893 p = d1893 q := by
  simp only [d1893, h 133 (by decide), agree1886 p q h, agree1872 p q h]
theorem nonnegative1893 (p : Pattern) : 0 ≤ d1893 p :=
  nonnegative_ite (p 133) (nonnegative1886 p) (nonnegative1872 p)
def d1894 (p : Pattern) : Int := if p 132 then d1893 p else d1873 p
theorem agree1894 (p q : Pattern) (h : Agree support p q) : d1894 p = d1894 q := by
  simp only [d1894, h 132 (by decide), agree1893 p q h, agree1873 p q h]
theorem nonnegative1894 (p : Pattern) : 0 ≤ d1894 p :=
  nonnegative_ite (p 132) (nonnegative1893 p) (nonnegative1873 p)
def d1895 (p : Pattern) : Int := if p 133 then d1886 p else d1880 p
theorem agree1895 (p q : Pattern) (h : Agree support p q) : d1895 p = d1895 q := by
  simp only [d1895, h 133 (by decide), agree1886 p q h, agree1880 p q h]
theorem nonnegative1895 (p : Pattern) : 0 ≤ d1895 p :=
  nonnegative_ite (p 133) (nonnegative1886 p) (nonnegative1880 p)
def d1896 (p : Pattern) : Int := if p 132 then d1895 p else d1881 p
theorem agree1896 (p q : Pattern) (h : Agree support p q) : d1896 p = d1896 q := by
  simp only [d1896, h 132 (by decide), agree1895 p q h, agree1881 p q h]
theorem nonnegative1896 (p : Pattern) : 0 ≤ d1896 p :=
  nonnegative_ite (p 132) (nonnegative1895 p) (nonnegative1881 p)
def d1897 (p : Pattern) : Int := if p 113 then d1896 p else d1894 p
theorem agree1897 (p q : Pattern) (h : Agree support p q) : d1897 p = d1897 q := by
  simp only [d1897, h 113 (by decide), agree1896 p q h, agree1894 p q h]
theorem nonnegative1897 (p : Pattern) : 0 ≤ d1897 p :=
  nonnegative_ite (p 113) (nonnegative1896 p) (nonnegative1894 p)
def d1898 (p : Pattern) : Int := if p 112 then d1897 p else d1892 p
theorem agree1898 (p q : Pattern) (h : Agree support p q) : d1898 p = d1898 q := by
  simp only [d1898, h 112 (by decide), agree1897 p q h, agree1892 p q h]
theorem nonnegative1898 (p : Pattern) : 0 ≤ d1898 p :=
  nonnegative_ite (p 112) (nonnegative1897 p) (nonnegative1892 p)
def d1899 (p : Pattern) : Int := if p 106 then d1898 p else d1885 p
theorem agree1899 (p q : Pattern) (h : Agree support p q) : d1899 p = d1899 q := by
  simp only [d1899, h 106 (by decide), agree1898 p q h, agree1885 p q h]
theorem nonnegative1899 (p : Pattern) : 0 ≤ d1899 p :=
  nonnegative_ite (p 106) (nonnegative1898 p) (nonnegative1885 p)
def d1900 (p : Pattern) : Int := if p 138 then d1876 p else d1554 p
theorem agree1900 (p q : Pattern) (h : Agree support p q) : d1900 p = d1900 q := by
  simp only [d1900, h 138 (by decide), agree1876 p q h, agree1554 p q h]
theorem nonnegative1900 (p : Pattern) : 0 ≤ d1900 p :=
  nonnegative_ite (p 138) (nonnegative1876 p) (nonnegative1554 p)
def d1901 (p : Pattern) : Int := if p 138 then d1878 p else d1864 p
theorem agree1901 (p q : Pattern) (h : Agree support p q) : d1901 p = d1901 q := by
  simp only [d1901, h 138 (by decide), agree1878 p q h, agree1864 p q h]
theorem nonnegative1901 (p : Pattern) : 0 ≤ d1901 p :=
  nonnegative_ite (p 138) (nonnegative1878 p) (nonnegative1864 p)
def d1902 (p : Pattern) : Int := if p 134 then d1901 p else d1900 p
theorem agree1902 (p q : Pattern) (h : Agree support p q) : d1902 p = d1902 q := by
  simp only [d1902, h 134 (by decide), agree1901 p q h, agree1900 p q h]
theorem nonnegative1902 (p : Pattern) : 0 ≤ d1902 p :=
  nonnegative_ite (p 134) (nonnegative1901 p) (nonnegative1900 p)
def d1903 (p : Pattern) : Int := if p 133 then d1902 p else d1900 p
theorem agree1903 (p q : Pattern) (h : Agree support p q) : d1903 p = d1903 q := by
  simp only [d1903, h 133 (by decide), agree1902 p q h, agree1900 p q h]
theorem nonnegative1903 (p : Pattern) : 0 ≤ d1903 p :=
  nonnegative_ite (p 133) (nonnegative1902 p) (nonnegative1900 p)
def d1904 (p : Pattern) : Int := if p 133 then d1901 p else d1902 p
theorem agree1904 (p q : Pattern) (h : Agree support p q) : d1904 p = d1904 q := by
  simp only [d1904, h 133 (by decide), agree1901 p q h, agree1902 p q h]
theorem nonnegative1904 (p : Pattern) : 0 ≤ d1904 p :=
  nonnegative_ite (p 133) (nonnegative1901 p) (nonnegative1902 p)
def d1905 (p : Pattern) : Int := if p 132 then d1904 p else d1903 p
theorem agree1905 (p q : Pattern) (h : Agree support p q) : d1905 p = d1905 q := by
  simp only [d1905, h 132 (by decide), agree1904 p q h, agree1903 p q h]
theorem nonnegative1905 (p : Pattern) : 0 ≤ d1905 p :=
  nonnegative_ite (p 132) (nonnegative1904 p) (nonnegative1903 p)
def d1906 (p : Pattern) : Int := if p 113 then d1905 p else d1871 p
theorem agree1906 (p q : Pattern) (h : Agree support p q) : d1906 p = d1906 q := by
  simp only [d1906, h 113 (by decide), agree1905 p q h, agree1871 p q h]
theorem nonnegative1906 (p : Pattern) : 0 ≤ d1906 p :=
  nonnegative_ite (p 113) (nonnegative1905 p) (nonnegative1871 p)
def d1907 (p : Pattern) : Int := if p 139 then d2 p else d1556 p
theorem agree1907 (p q : Pattern) (h : Agree support p q) : d1907 p = d1907 q := by
  simp only [d1907, h 139 (by decide), agree2 p q h, agree1556 p q h]
theorem nonnegative1907 (p : Pattern) : 0 ≤ d1907 p :=
  nonnegative_ite (p 139) (nonnegative2 p) (nonnegative1556 p)
def d1908 (p : Pattern) : Int := if p 138 then d1907 p else d1556 p
theorem agree1908 (p q : Pattern) (h : Agree support p q) : d1908 p = d1908 q := by
  simp only [d1908, h 138 (by decide), agree1907 p q h, agree1556 p q h]
theorem nonnegative1908 (p : Pattern) : 0 ≤ d1908 p :=
  nonnegative_ite (p 138) (nonnegative1907 p) (nonnegative1556 p)
def d1909 (p : Pattern) : Int := if p 134 then d1887 p else d1908 p
theorem agree1909 (p q : Pattern) (h : Agree support p q) : d1909 p = d1909 q := by
  simp only [d1909, h 134 (by decide), agree1887 p q h, agree1908 p q h]
theorem nonnegative1909 (p : Pattern) : 0 ≤ d1909 p :=
  nonnegative_ite (p 134) (nonnegative1887 p) (nonnegative1908 p)
def d1910 (p : Pattern) : Int := if p 133 then d1909 p else d1908 p
theorem agree1910 (p q : Pattern) (h : Agree support p q) : d1910 p = d1910 q := by
  simp only [d1910, h 133 (by decide), agree1909 p q h, agree1908 p q h]
theorem nonnegative1910 (p : Pattern) : 0 ≤ d1910 p :=
  nonnegative_ite (p 133) (nonnegative1909 p) (nonnegative1908 p)
def d1911 (p : Pattern) : Int := if p 133 then d1887 p else d1909 p
theorem agree1911 (p q : Pattern) (h : Agree support p q) : d1911 p = d1911 q := by
  simp only [d1911, h 133 (by decide), agree1887 p q h, agree1909 p q h]
theorem nonnegative1911 (p : Pattern) : 0 ≤ d1911 p :=
  nonnegative_ite (p 133) (nonnegative1887 p) (nonnegative1909 p)
def d1912 (p : Pattern) : Int := if p 132 then d1911 p else d1910 p
theorem agree1912 (p q : Pattern) (h : Agree support p q) : d1912 p = d1912 q := by
  simp only [d1912, h 132 (by decide), agree1911 p q h, agree1910 p q h]
theorem nonnegative1912 (p : Pattern) : 0 ≤ d1912 p :=
  nonnegative_ite (p 132) (nonnegative1911 p) (nonnegative1910 p)
def d1913 (p : Pattern) : Int := if p 112 then d1912 p else d1906 p
theorem agree1913 (p q : Pattern) (h : Agree support p q) : d1913 p = d1913 q := by
  simp only [d1913, h 112 (by decide), agree1912 p q h, agree1906 p q h]
theorem nonnegative1913 (p : Pattern) : 0 ≤ d1913 p :=
  nonnegative_ite (p 112) (nonnegative1912 p) (nonnegative1906 p)
def d1914 (p : Pattern) : Int := if p 133 then d1886 p else d1902 p
theorem agree1914 (p q : Pattern) (h : Agree support p q) : d1914 p = d1914 q := by
  simp only [d1914, h 133 (by decide), agree1886 p q h, agree1902 p q h]
theorem nonnegative1914 (p : Pattern) : 0 ≤ d1914 p :=
  nonnegative_ite (p 133) (nonnegative1886 p) (nonnegative1902 p)
def d1915 (p : Pattern) : Int := if p 132 then d1914 p else d1903 p
theorem agree1915 (p q : Pattern) (h : Agree support p q) : d1915 p = d1915 q := by
  simp only [d1915, h 132 (by decide), agree1914 p q h, agree1903 p q h]
theorem nonnegative1915 (p : Pattern) : 0 ≤ d1915 p :=
  nonnegative_ite (p 132) (nonnegative1914 p) (nonnegative1903 p)
def d1916 (p : Pattern) : Int := if p 113 then d1915 p else d1891 p
theorem agree1916 (p q : Pattern) (h : Agree support p q) : d1916 p = d1916 q := by
  simp only [d1916, h 113 (by decide), agree1915 p q h, agree1891 p q h]
theorem nonnegative1916 (p : Pattern) : 0 ≤ d1916 p :=
  nonnegative_ite (p 113) (nonnegative1915 p) (nonnegative1891 p)
def d1917 (p : Pattern) : Int := if p 133 then d2 p else d1909 p
theorem agree1917 (p q : Pattern) (h : Agree support p q) : d1917 p = d1917 q := by
  simp only [d1917, h 133 (by decide), agree2 p q h, agree1909 p q h]
theorem nonnegative1917 (p : Pattern) : 0 ≤ d1917 p :=
  nonnegative_ite (p 133) (nonnegative2 p) (nonnegative1909 p)
def d1918 (p : Pattern) : Int := if p 132 then d1917 p else d1910 p
theorem agree1918 (p q : Pattern) (h : Agree support p q) : d1918 p = d1918 q := by
  simp only [d1918, h 132 (by decide), agree1917 p q h, agree1910 p q h]
theorem nonnegative1918 (p : Pattern) : 0 ≤ d1918 p :=
  nonnegative_ite (p 132) (nonnegative1917 p) (nonnegative1910 p)
def d1919 (p : Pattern) : Int := if p 134 then d1886 p else d1907 p
theorem agree1919 (p q : Pattern) (h : Agree support p q) : d1919 p = d1919 q := by
  simp only [d1919, h 134 (by decide), agree1886 p q h, agree1907 p q h]
theorem nonnegative1919 (p : Pattern) : 0 ≤ d1919 p :=
  nonnegative_ite (p 134) (nonnegative1886 p) (nonnegative1907 p)
end NetHack.Sokoban32Refined
