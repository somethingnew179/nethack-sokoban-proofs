/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1800 (p : Pattern) : d13 (change p 10000 (some 115)) = d13 p := by
  change (if p 247 then d12 (change p 10000 (some 115)) else d0 (change p 10000 (some 115))) = d13 p
  rw [sub1799, sub1798]
  rfl
theorem sub1801 (p : Pattern) : d14 (change p 10000 (some 115)) = d14 p := by
  change (if p 246 then d13 (change p 10000 (some 115)) else d0 (change p 10000 (some 115))) = d14 p
  rw [sub1800, sub1798]
  rfl
theorem sub1802 (p : Pattern) : d15 (change p 10000 (some 115)) = d15 p := by
  change (if p 204 then d12 (change p 10000 (some 115)) else d14 (change p 10000 (some 115))) = d15 p
  rw [sub1799, sub1801]
  rfl
theorem sub1803 (p : Pattern) : d16 (change p 10000 (some 115)) = d16 p := by
  change (if p 182 then d15 (change p 10000 (some 115)) else d14 (change p 10000 (some 115))) = d16 p
  rw [sub1802, sub1801]
  rfl
theorem sub1804 (p : Pattern) : d4 (change p 10000 (some 115)) = d4 p := by
  rfl
theorem sub1805 (p : Pattern) : d17 (change p 10000 (some 115)) = d17 p := by
  change (if p 247 then d12 (change p 10000 (some 115)) else d4 (change p 10000 (some 115))) = d17 p
  rw [sub1799, sub1804]
  rfl
theorem sub1806 (p : Pattern) : d18 (change p 10000 (some 115)) = d18 p := by
  change (if p 246 then d17 (change p 10000 (some 115)) else d4 (change p 10000 (some 115))) = d18 p
  rw [sub1805, sub1804]
  rfl
theorem sub1807 (p : Pattern) : d19 (change p 10000 (some 115)) = d19 p := by
  change (if p 204 then d12 (change p 10000 (some 115)) else d18 (change p 10000 (some 115))) = d19 p
  rw [sub1799, sub1806]
  rfl
theorem sub1808 (p : Pattern) : d20 (change p 10000 (some 115)) = d20 p := by
  change (if p 182 then d19 (change p 10000 (some 115)) else d18 (change p 10000 (some 115))) = d20 p
  rw [sub1807, sub1806]
  rfl
theorem sub1809 (p : Pattern) : d21 (change p 10000 (some 115)) = d21 p := by
  change (if p 163 then d20 (change p 10000 (some 115)) else d16 (change p 10000 (some 115))) = d21 p
  rw [sub1808, sub1803]
  rfl
theorem sub1810 (p : Pattern) : d22 (change p 10000 (some 115)) = d22 p := by
  change (if p 162 then d21 (change p 10000 (some 115)) else d16 (change p 10000 (some 115))) = d22 p
  rw [sub1809, sub1803]
  rfl
theorem sub1811 (p : Pattern) : d9 (change p 10000 (some 115)) = d9 p := by
  rfl
theorem sub1812 (p : Pattern) : d23 (change p 10000 (some 115)) = d23 p := by
  change (if p 247 then d12 (change p 10000 (some 115)) else d9 (change p 10000 (some 115))) = d23 p
  rw [sub1799, sub1811]
  rfl
theorem sub1813 (p : Pattern) : d24 (change p 10000 (some 115)) = d24 p := by
  change (if p 246 then d23 (change p 10000 (some 115)) else d9 (change p 10000 (some 115))) = d24 p
  rw [sub1812, sub1811]
  rfl
theorem sub1814 (p : Pattern) : d25 (change p 10000 (some 115)) = d25 p := by
  change (if p 204 then d12 (change p 10000 (some 115)) else d24 (change p 10000 (some 115))) = d25 p
  rw [sub1799, sub1813]
  rfl
theorem sub1815 (p : Pattern) : d26 (change p 10000 (some 115)) = d26 p := by
  change (if p 182 then d25 (change p 10000 (some 115)) else d24 (change p 10000 (some 115))) = d26 p
  rw [sub1814, sub1813]
  rfl
theorem sub1816 (p : Pattern) : d27 (change p 10000 (some 115)) = d27 p := by
  change (if p 163 then d12 (change p 10000 (some 115)) else d26 (change p 10000 (some 115))) = d27 p
  rw [sub1799, sub1815]
  rfl
theorem sub1817 (p : Pattern) : d28 (change p 10000 (some 115)) = d28 p := by
  change (if p 162 then d27 (change p 10000 (some 115)) else d21 (change p 10000 (some 115))) = d28 p
  rw [sub1816, sub1809]
  rfl
theorem sub1818 (p : Pattern) : d29 (change p 10000 (some 115)) = d29 p := by
  change (if p 161 then d28 (change p 10000 (some 115)) else d22 (change p 10000 (some 115))) = d29 p
  rw [sub1817, sub1810]
  rfl
theorem sub1819 (p : Pattern) : d2 (change p 10000 (some 115)) = d2 p := by
  rfl
theorem sub1820 (p : Pattern) : d30 (change p 10000 (some 115)) = d30 p := by
  change (if p 247 then d12 (change p 10000 (some 115)) else d2 (change p 10000 (some 115))) = d30 p
  rw [sub1799, sub1819]
  rfl
theorem sub1821 (p : Pattern) : d31 (change p 10000 (some 115)) = d31 p := by
  change (if p 246 then d30 (change p 10000 (some 115)) else d2 (change p 10000 (some 115))) = d31 p
  rw [sub1820, sub1819]
  rfl
theorem sub1822 (p : Pattern) : d32 (change p 10000 (some 115)) = d32 p := by
  change (if p 204 then d12 (change p 10000 (some 115)) else d31 (change p 10000 (some 115))) = d32 p
  rw [sub1799, sub1821]
  rfl
theorem sub1823 (p : Pattern) : d33 (change p 10000 (some 115)) = d33 p := by
  change (if p 182 then d32 (change p 10000 (some 115)) else d14 (change p 10000 (some 115))) = d33 p
  rw [sub1822, sub1801]
  rfl
theorem sub1824 (p : Pattern) : d6 (change p 10000 (some 115)) = d6 p := by
  rfl
theorem sub1825 (p : Pattern) : d34 (change p 10000 (some 115)) = d34 p := by
  change (if p 247 then d12 (change p 10000 (some 115)) else d6 (change p 10000 (some 115))) = d34 p
  rw [sub1799, sub1824]
  rfl
theorem sub1826 (p : Pattern) : d35 (change p 10000 (some 115)) = d35 p := by
  change (if p 246 then d34 (change p 10000 (some 115)) else d6 (change p 10000 (some 115))) = d35 p
  rw [sub1825, sub1824]
  rfl
theorem sub1827 (p : Pattern) : d36 (change p 10000 (some 115)) = d36 p := by
  change (if p 204 then d12 (change p 10000 (some 115)) else d35 (change p 10000 (some 115))) = d36 p
  rw [sub1799, sub1826]
  rfl
theorem sub1828 (p : Pattern) : d37 (change p 10000 (some 115)) = d37 p := by
  change (if p 182 then d36 (change p 10000 (some 115)) else d14 (change p 10000 (some 115))) = d37 p
  rw [sub1827, sub1801]
  rfl
theorem sub1829 (p : Pattern) : d38 (change p 10000 (some 115)) = d38 p := by
  change (if p 163 then d37 (change p 10000 (some 115)) else d33 (change p 10000 (some 115))) = d38 p
  rw [sub1828, sub1823]
  rfl
theorem sub1830 (p : Pattern) : d11 (change p 10000 (some 115)) = d11 p := by
  rfl
theorem sub1831 (p : Pattern) : d39 (change p 10000 (some 115)) = d39 p := by
  change (if p 247 then d12 (change p 10000 (some 115)) else d11 (change p 10000 (some 115))) = d39 p
  rw [sub1799, sub1830]
  rfl
theorem sub1832 (p : Pattern) : d40 (change p 10000 (some 115)) = d40 p := by
  change (if p 246 then d39 (change p 10000 (some 115)) else d11 (change p 10000 (some 115))) = d40 p
  rw [sub1831, sub1830]
  rfl
theorem sub1833 (p : Pattern) : d41 (change p 10000 (some 115)) = d41 p := by
  change (if p 204 then d12 (change p 10000 (some 115)) else d40 (change p 10000 (some 115))) = d41 p
  rw [sub1799, sub1832]
  rfl
theorem sub1834 (p : Pattern) : d42 (change p 10000 (some 115)) = d42 p := by
  change (if p 182 then d41 (change p 10000 (some 115)) else d14 (change p 10000 (some 115))) = d42 p
  rw [sub1833, sub1801]
  rfl
theorem sub1835 (p : Pattern) : d43 (change p 10000 (some 115)) = d43 p := by
  change (if p 182 then d12 (change p 10000 (some 115)) else d18 (change p 10000 (some 115))) = d43 p
  rw [sub1799, sub1806]
  rfl
theorem sub1836 (p : Pattern) : d44 (change p 10000 (some 115)) = d44 p := by
  change (if p 163 then d43 (change p 10000 (some 115)) else d42 (change p 10000 (some 115))) = d44 p
  rw [sub1835, sub1834]
  rfl
theorem sub1837 (p : Pattern) : d45 (change p 10000 (some 115)) = d45 p := by
  change (if p 162 then d44 (change p 10000 (some 115)) else d38 (change p 10000 (some 115))) = d45 p
  rw [sub1836, sub1829]
  rfl
theorem sub1838 (p : Pattern) : d46 (change p 10000 (some 115)) = d46 p := by
  change (if p 182 then d12 (change p 10000 (some 115)) else d14 (change p 10000 (some 115))) = d46 p
  rw [sub1799, sub1801]
  rfl
theorem sub1839 (p : Pattern) : d47 (change p 10000 (some 115)) = d47 p := by
  change (if p 163 then d43 (change p 10000 (some 115)) else d46 (change p 10000 (some 115))) = d47 p
  rw [sub1835, sub1838]
  rfl
theorem sub1840 (p : Pattern) : d48 (change p 10000 (some 115)) = d48 p := by
  change (if p 182 then d12 (change p 10000 (some 115)) else d24 (change p 10000 (some 115))) = d48 p
  rw [sub1799, sub1813]
  rfl
theorem sub1841 (p : Pattern) : d49 (change p 10000 (some 115)) = d49 p := by
  change (if p 163 then d12 (change p 10000 (some 115)) else d48 (change p 10000 (some 115))) = d49 p
  rw [sub1799, sub1840]
  rfl
theorem sub1842 (p : Pattern) : d50 (change p 10000 (some 115)) = d50 p := by
  change (if p 162 then d49 (change p 10000 (some 115)) else d47 (change p 10000 (some 115))) = d50 p
  rw [sub1841, sub1839]
  rfl
theorem sub1843 (p : Pattern) : d51 (change p 10000 (some 115)) = d51 p := by
  change (if p 161 then d50 (change p 10000 (some 115)) else d45 (change p 10000 (some 115))) = d51 p
  rw [sub1842, sub1837]
  rfl
theorem sub1844 (p : Pattern) : d52 (change p 10000 (some 115)) = d52 p := by
  change (if p 160 then d51 (change p 10000 (some 115)) else d29 (change p 10000 (some 115))) = d52 p
  rw [sub1843, sub1818]
  rfl
theorem sub1845 (p : Pattern) : d53 (change p 10000 (some 115)) = d53 p := by
  change (if p 182 then d32 (change p 10000 (some 115)) else d31 (change p 10000 (some 115))) = d53 p
  rw [sub1822, sub1821]
  rfl
theorem sub1846 (p : Pattern) : d54 (change p 10000 (some 115)) = d54 p := by
  change (if p 163 then d53 (change p 10000 (some 115)) else d16 (change p 10000 (some 115))) = d54 p
  rw [sub1845, sub1803]
  rfl
theorem sub1847 (p : Pattern) : d55 (change p 10000 (some 115)) = d55 p := by
  change (if p 163 then d26 (change p 10000 (some 115)) else d20 (change p 10000 (some 115))) = d55 p
  rw [sub1815, sub1808]
  rfl
theorem sub1848 (p : Pattern) : d56 (change p 10000 (some 115)) = d56 p := by
  change (if p 162 then d55 (change p 10000 (some 115)) else d54 (change p 10000 (some 115))) = d56 p
  rw [sub1847, sub1846]
  rfl
theorem sub1849 (p : Pattern) : d10 (change p 10000 (some 115)) = d10 p := by
  rfl
theorem sub1850 (p : Pattern) : d57 (change p 10000 (some 115)) = d57 p := by
  change (if p 247 then d12 (change p 10000 (some 115)) else d10 (change p 10000 (some 115))) = d57 p
  rw [sub1799, sub1849]
  rfl
theorem sub1851 (p : Pattern) : d58 (change p 10000 (some 115)) = d58 p := by
  change (if p 246 then d57 (change p 10000 (some 115)) else d10 (change p 10000 (some 115))) = d58 p
  rw [sub1850, sub1849]
  rfl
theorem sub1852 (p : Pattern) : d59 (change p 10000 (some 115)) = d59 p := by
  change (if p 204 then d12 (change p 10000 (some 115)) else d58 (change p 10000 (some 115))) = d59 p
  rw [sub1799, sub1851]
  rfl
theorem sub1853 (p : Pattern) : d60 (change p 10000 (some 115)) = d60 p := by
  change (if p 182 then d59 (change p 10000 (some 115)) else d58 (change p 10000 (some 115))) = d60 p
  rw [sub1852, sub1851]
  rfl
theorem sub1854 (p : Pattern) : d61 (change p 10000 (some 115)) = d61 p := by
  change (if p 163 then d60 (change p 10000 (some 115)) else d20 (change p 10000 (some 115))) = d61 p
  rw [sub1853, sub1808]
  rfl
theorem sub1855 (p : Pattern) : d62 (change p 10000 (some 115)) = d62 p := by
  change (if p 182 then d41 (change p 10000 (some 115)) else d40 (change p 10000 (some 115))) = d62 p
  rw [sub1833, sub1832]
  rfl
theorem sub1856 (p : Pattern) : d63 (change p 10000 (some 115)) = d63 p := by
  change (if p 163 then d12 (change p 10000 (some 115)) else d62 (change p 10000 (some 115))) = d63 p
  rw [sub1799, sub1855]
  rfl
theorem sub1857 (p : Pattern) : d64 (change p 10000 (some 115)) = d64 p := by
  change (if p 162 then d63 (change p 10000 (some 115)) else d61 (change p 10000 (some 115))) = d64 p
  rw [sub1856, sub1854]
  rfl
theorem sub1858 (p : Pattern) : d65 (change p 10000 (some 115)) = d65 p := by
  change (if p 161 then d64 (change p 10000 (some 115)) else d56 (change p 10000 (some 115))) = d65 p
  rw [sub1857, sub1848]
  rfl
theorem sub1859 (p : Pattern) : d66 (change p 10000 (some 115)) = d66 p := by
  change (if p 182 then d12 (change p 10000 (some 115)) else d31 (change p 10000 (some 115))) = d66 p
  rw [sub1799, sub1821]
  rfl
theorem sub1860 (p : Pattern) : d67 (change p 10000 (some 115)) = d67 p := by
  change (if p 163 then d66 (change p 10000 (some 115)) else d37 (change p 10000 (some 115))) = d67 p
  rw [sub1859, sub1828]
  rfl
theorem sub1861 (p : Pattern) : d68 (change p 10000 (some 115)) = d68 p := by
  change (if p 163 then d48 (change p 10000 (some 115)) else d43 (change p 10000 (some 115))) = d68 p
  rw [sub1840, sub1835]
  rfl
theorem sub1862 (p : Pattern) : d69 (change p 10000 (some 115)) = d69 p := by
  change (if p 162 then d68 (change p 10000 (some 115)) else d67 (change p 10000 (some 115))) = d69 p
  rw [sub1861, sub1860]
  rfl
theorem sub1863 (p : Pattern) : d70 (change p 10000 (some 115)) = d70 p := by
  change (if p 182 then d12 (change p 10000 (some 115)) else d58 (change p 10000 (some 115))) = d70 p
  rw [sub1799, sub1851]
  rfl
theorem sub1864 (p : Pattern) : d71 (change p 10000 (some 115)) = d71 p := by
  change (if p 163 then d70 (change p 10000 (some 115)) else d43 (change p 10000 (some 115))) = d71 p
  rw [sub1863, sub1835]
  rfl
theorem sub1865 (p : Pattern) : d72 (change p 10000 (some 115)) = d72 p := by
  change (if p 182 then d12 (change p 10000 (some 115)) else d40 (change p 10000 (some 115))) = d72 p
  rw [sub1799, sub1832]
  rfl
theorem sub1866 (p : Pattern) : d73 (change p 10000 (some 115)) = d73 p := by
  change (if p 163 then d12 (change p 10000 (some 115)) else d72 (change p 10000 (some 115))) = d73 p
  rw [sub1799, sub1865]
  rfl
theorem sub1867 (p : Pattern) : d74 (change p 10000 (some 115)) = d74 p := by
  change (if p 162 then d73 (change p 10000 (some 115)) else d71 (change p 10000 (some 115))) = d74 p
  rw [sub1866, sub1864]
  rfl
theorem sub1868 (p : Pattern) : d75 (change p 10000 (some 115)) = d75 p := by
  change (if p 161 then d74 (change p 10000 (some 115)) else d69 (change p 10000 (some 115))) = d75 p
  rw [sub1867, sub1862]
  rfl
theorem sub1869 (p : Pattern) : d76 (change p 10000 (some 115)) = d76 p := by
  change (if p 160 then d75 (change p 10000 (some 115)) else d65 (change p 10000 (some 115))) = d76 p
  rw [sub1868, sub1858]
  rfl
theorem sub1870 (p : Pattern) : d77 (change p 10000 (some 115)) = d77 p := by
  change (if p 141 then d76 (change p 10000 (some 115)) else d52 (change p 10000 (some 115))) = d77 p
  rw [sub1869, sub1844]
  rfl
theorem sub1871 (p : Pattern) : d78 (change p 10000 (some 115)) = d78 p := by
  change (if p 182 then d36 (change p 10000 (some 115)) else d35 (change p 10000 (some 115))) = d78 p
  rw [sub1827, sub1826]
  rfl
theorem sub1872 (p : Pattern) : d79 (change p 10000 (some 115)) = d79 p := by
  change (if p 163 then d78 (change p 10000 (some 115)) else d53 (change p 10000 (some 115))) = d79 p
  rw [sub1871, sub1845]
  rfl
theorem sub1873 (p : Pattern) : d80 (change p 10000 (some 115)) = d80 p := by
  change (if p 162 then d63 (change p 10000 (some 115)) else d79 (change p 10000 (some 115))) = d80 p
  rw [sub1856, sub1872]
  rfl
theorem sub1874 (p : Pattern) : d81 (change p 10000 (some 115)) = d81 p := by
  change (if p 161 then d12 (change p 10000 (some 115)) else d80 (change p 10000 (some 115))) = d81 p
  rw [sub1799, sub1873]
  rfl
theorem sub1875 (p : Pattern) : d82 (change p 10000 (some 115)) = d82 p := by
  change (if p 160 then d81 (change p 10000 (some 115)) else d29 (change p 10000 (some 115))) = d82 p
  rw [sub1874, sub1818]
  rfl
theorem sub1876 (p : Pattern) : d83 (change p 10000 (some 115)) = d83 p := by
  change (if p 163 then d12 (change p 10000 (some 115)) else d78 (change p 10000 (some 115))) = d83 p
  rw [sub1799, sub1871]
  rfl
theorem sub1877 (p : Pattern) : d84 (change p 10000 (some 115)) = d84 p := by
  change (if p 162 then d12 (change p 10000 (some 115)) else d83 (change p 10000 (some 115))) = d84 p
  rw [sub1799, sub1876]
  rfl
theorem sub1878 (p : Pattern) : d85 (change p 10000 (some 115)) = d85 p := by
  change (if p 161 then d12 (change p 10000 (some 115)) else d84 (change p 10000 (some 115))) = d85 p
  rw [sub1799, sub1877]
  rfl
theorem sub1879 (p : Pattern) : d86 (change p 10000 (some 115)) = d86 p := by
  change (if p 160 then d85 (change p 10000 (some 115)) else d65 (change p 10000 (some 115))) = d86 p
  rw [sub1878, sub1858]
  rfl
theorem sub1880 (p : Pattern) : d87 (change p 10000 (some 115)) = d87 p := by
  change (if p 141 then d86 (change p 10000 (some 115)) else d82 (change p 10000 (some 115))) = d87 p
  rw [sub1879, sub1875]
  rfl
theorem sub1881 (p : Pattern) : d88 (change p 10000 (some 115)) = d88 p := by
  change (if p 138 then d87 (change p 10000 (some 115)) else d77 (change p 10000 (some 115))) = d88 p
  rw [sub1880, sub1870]
  rfl
theorem sub1882 (p : Pattern) : d99 (change p 10000 (some 115)) = d99 p := by
  change (if p 138 then d12 (change p 10000 (some 115)) else d87 (change p 10000 (some 115))) = d99 p
  rw [sub1799, sub1880]
  rfl
theorem sub1883 (p : Pattern) : d100 (change p 10000 (some 115)) = d100 p := by
  change (if p 116 then d99 (change p 10000 (some 115)) else d88 (change p 10000 (some 115))) = d100 p
  rw [sub1882, sub1881]
  rfl
theorem sub1884 (p : Pattern) : d101 (change p 10000 (some 115)) = d100 p := by
  change d100 (change p 10000 (some 115)) = d100 p
  exact sub1883 p
theorem sub1885 (p : Pattern) : d1 (change p 10000 (some 115)) = d1 p := by
  rfl
theorem sub1886 (p : Pattern) : d102 (change p 10000 (some 115)) = d102 p := by
  change (if p 247 then d12 (change p 10000 (some 115)) else d1 (change p 10000 (some 115))) = d102 p
  rw [sub1799, sub1885]
  rfl
theorem sub1887 (p : Pattern) : d103 (change p 10000 (some 115)) = d103 p := by
  change (if p 246 then d102 (change p 10000 (some 115)) else d1 (change p 10000 (some 115))) = d103 p
  rw [sub1886, sub1885]
  rfl
theorem sub1888 (p : Pattern) : d104 (change p 10000 (some 115)) = d104 p := by
  change (if p 204 then d12 (change p 10000 (some 115)) else d103 (change p 10000 (some 115))) = d104 p
  rw [sub1799, sub1887]
  rfl
theorem sub1889 (p : Pattern) : d105 (change p 10000 (some 115)) = d105 p := by
  change (if p 182 then d104 (change p 10000 (some 115)) else d103 (change p 10000 (some 115))) = d105 p
  rw [sub1888, sub1887]
  rfl
theorem sub1890 (p : Pattern) : d5 (change p 10000 (some 115)) = d5 p := by
  rfl
theorem sub1891 (p : Pattern) : d106 (change p 10000 (some 115)) = d106 p := by
  change (if p 247 then d12 (change p 10000 (some 115)) else d5 (change p 10000 (some 115))) = d106 p
  rw [sub1799, sub1890]
  rfl
theorem sub1892 (p : Pattern) : d107 (change p 10000 (some 115)) = d107 p := by
  change (if p 246 then d106 (change p 10000 (some 115)) else d5 (change p 10000 (some 115))) = d107 p
  rw [sub1891, sub1890]
  rfl
theorem sub1893 (p : Pattern) : d108 (change p 10000 (some 115)) = d108 p := by
  change (if p 204 then d12 (change p 10000 (some 115)) else d107 (change p 10000 (some 115))) = d108 p
  rw [sub1799, sub1892]
  rfl
theorem sub1894 (p : Pattern) : d109 (change p 10000 (some 115)) = d109 p := by
  change (if p 182 then d108 (change p 10000 (some 115)) else d107 (change p 10000 (some 115))) = d109 p
  rw [sub1893, sub1892]
  rfl
theorem sub1895 (p : Pattern) : d110 (change p 10000 (some 115)) = d110 p := by
  change (if p 163 then d109 (change p 10000 (some 115)) else d105 (change p 10000 (some 115))) = d110 p
  rw [sub1894, sub1889]
  rfl
theorem sub1896 (p : Pattern) : d111 (change p 10000 (some 115)) = d111 p := by
  change (if p 162 then d110 (change p 10000 (some 115)) else d105 (change p 10000 (some 115))) = d111 p
  rw [sub1895, sub1889]
  rfl
theorem sub1897 (p : Pattern) : d112 (change p 10000 (some 115)) = d112 p := by
  change (if p 163 then d12 (change p 10000 (some 115)) else d60 (change p 10000 (some 115))) = d112 p
  rw [sub1799, sub1853]
  rfl
theorem sub1898 (p : Pattern) : d113 (change p 10000 (some 115)) = d113 p := by
  change (if p 162 then d112 (change p 10000 (some 115)) else d110 (change p 10000 (some 115))) = d113 p
  rw [sub1897, sub1895]
  rfl
theorem sub1899 (p : Pattern) : d114 (change p 10000 (some 115)) = d114 p := by
  change (if p 161 then d113 (change p 10000 (some 115)) else d111 (change p 10000 (some 115))) = d114 p
  rw [sub1898, sub1896]
  rfl
theorem sub1900 (p : Pattern) : d3 (change p 10000 (some 115)) = d3 p := by
  rfl
theorem sub1901 (p : Pattern) : d115 (change p 10000 (some 115)) = d115 p := by
  change (if p 247 then d12 (change p 10000 (some 115)) else d3 (change p 10000 (some 115))) = d115 p
  rw [sub1799, sub1900]
  rfl
theorem sub1902 (p : Pattern) : d116 (change p 10000 (some 115)) = d116 p := by
  change (if p 246 then d115 (change p 10000 (some 115)) else d3 (change p 10000 (some 115))) = d116 p
  rw [sub1901, sub1900]
  rfl
theorem sub1903 (p : Pattern) : d117 (change p 10000 (some 115)) = d117 p := by
  change (if p 204 then d12 (change p 10000 (some 115)) else d116 (change p 10000 (some 115))) = d117 p
  rw [sub1799, sub1902]
  rfl
theorem sub1904 (p : Pattern) : d118 (change p 10000 (some 115)) = d118 p := by
  change (if p 182 then d117 (change p 10000 (some 115)) else d103 (change p 10000 (some 115))) = d118 p
  rw [sub1903, sub1887]
  rfl
theorem sub1905 (p : Pattern) : d7 (change p 10000 (some 115)) = d7 p := by
  rfl
theorem sub1906 (p : Pattern) : d119 (change p 10000 (some 115)) = d119 p := by
  change (if p 247 then d12 (change p 10000 (some 115)) else d7 (change p 10000 (some 115))) = d119 p
  rw [sub1799, sub1905]
  rfl
theorem sub1907 (p : Pattern) : d120 (change p 10000 (some 115)) = d120 p := by
  change (if p 246 then d119 (change p 10000 (some 115)) else d7 (change p 10000 (some 115))) = d120 p
  rw [sub1906, sub1905]
  rfl
theorem sub1908 (p : Pattern) : d121 (change p 10000 (some 115)) = d121 p := by
  change (if p 204 then d12 (change p 10000 (some 115)) else d120 (change p 10000 (some 115))) = d121 p
  rw [sub1799, sub1907]
  rfl
theorem sub1909 (p : Pattern) : d122 (change p 10000 (some 115)) = d122 p := by
  change (if p 182 then d121 (change p 10000 (some 115)) else d103 (change p 10000 (some 115))) = d122 p
  rw [sub1908, sub1887]
  rfl
theorem sub1910 (p : Pattern) : d123 (change p 10000 (some 115)) = d123 p := by
  change (if p 163 then d122 (change p 10000 (some 115)) else d118 (change p 10000 (some 115))) = d123 p
  rw [sub1909, sub1904]
  rfl
theorem sub1911 (p : Pattern) : d124 (change p 10000 (some 115)) = d124 p := by
  change (if p 182 then d12 (change p 10000 (some 115)) else d103 (change p 10000 (some 115))) = d124 p
  rw [sub1799, sub1887]
  rfl
theorem sub1912 (p : Pattern) : d125 (change p 10000 (some 115)) = d125 p := by
  change (if p 182 then d12 (change p 10000 (some 115)) else d107 (change p 10000 (some 115))) = d125 p
  rw [sub1799, sub1892]
  rfl
theorem sub1913 (p : Pattern) : d126 (change p 10000 (some 115)) = d126 p := by
  change (if p 163 then d125 (change p 10000 (some 115)) else d124 (change p 10000 (some 115))) = d126 p
  rw [sub1912, sub1911]
  rfl
theorem sub1914 (p : Pattern) : d127 (change p 10000 (some 115)) = d127 p := by
  change (if p 162 then d126 (change p 10000 (some 115)) else d123 (change p 10000 (some 115))) = d127 p
  rw [sub1913, sub1910]
  rfl
theorem sub1915 (p : Pattern) : d128 (change p 10000 (some 115)) = d128 p := by
  change (if p 163 then d12 (change p 10000 (some 115)) else d70 (change p 10000 (some 115))) = d128 p
  rw [sub1799, sub1863]
  rfl
theorem sub1916 (p : Pattern) : d129 (change p 10000 (some 115)) = d129 p := by
  change (if p 162 then d128 (change p 10000 (some 115)) else d126 (change p 10000 (some 115))) = d129 p
  rw [sub1915, sub1913]
  rfl
theorem sub1917 (p : Pattern) : d130 (change p 10000 (some 115)) = d130 p := by
  change (if p 161 then d129 (change p 10000 (some 115)) else d127 (change p 10000 (some 115))) = d130 p
  rw [sub1916, sub1914]
  rfl
theorem sub1918 (p : Pattern) : d131 (change p 10000 (some 115)) = d131 p := by
  change (if p 160 then d130 (change p 10000 (some 115)) else d114 (change p 10000 (some 115))) = d131 p
  rw [sub1917, sub1899]
  rfl
theorem sub1919 (p : Pattern) : d132 (change p 10000 (some 115)) = d132 p := by
  change (if p 182 then d117 (change p 10000 (some 115)) else d116 (change p 10000 (some 115))) = d132 p
  rw [sub1903, sub1902]
  rfl
end NetHack.Sokoban22Refined85
