/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1800 (p : Pattern) : d19 (change p 132 none) = d19 p := by
  change (if p 159 then d2 (change p 132 none) else d17 (change p 132 none)) = d19 p
  rw [sub1782, sub1798]
  rfl
theorem sub1801 (p : Pattern) : d20 (change p 132 none) = d20 p := by
  change (if p 158 then d19 (change p 132 none) else d18 (change p 132 none)) = d20 p
  rw [sub1800, sub1799]
  rfl
theorem sub1802 (p : Pattern) : d21 (change p 132 none) = d21 p := by
  change (if p 160 then d2 (change p 132 none) else d9 (change p 132 none)) = d21 p
  rw [sub1782, sub1790]
  rfl
theorem sub1803 (p : Pattern) : d22 (change p 132 none) = d22 p := by
  change (if p 159 then d21 (change p 132 none) else d10 (change p 132 none)) = d22 p
  rw [sub1802, sub1791]
  rfl
theorem sub1804 (p : Pattern) : d23 (change p 132 none) = d23 p := by
  change (if p 159 then d2 (change p 132 none) else d21 (change p 132 none)) = d23 p
  rw [sub1782, sub1802]
  rfl
theorem sub1805 (p : Pattern) : d24 (change p 132 none) = d24 p := by
  change (if p 158 then d23 (change p 132 none) else d22 (change p 132 none)) = d24 p
  rw [sub1804, sub1803]
  rfl
theorem sub1806 (p : Pattern) : d25 (change p 132 none) = d25 p := by
  change (if p 139 then d24 (change p 132 none) else d20 (change p 132 none)) = d25 p
  rw [sub1805, sub1801]
  rfl
theorem sub1807 (p : Pattern) : d26 (change p 132 none) = d26 p := by
  change (if p 138 then d25 (change p 132 none) else d20 (change p 132 none)) = d26 p
  rw [sub1806, sub1801]
  rfl
theorem sub1808 (p : Pattern) : d27 (change p 132 none) = d27 p := by
  change (if p 134 then d26 (change p 132 none) else d16 (change p 132 none)) = d27 p
  rw [sub1807, sub1797]
  rfl
theorem sub1809 (p : Pattern) : d28 (change p 132 none) = d28 p := by
  change (if p 133 then d27 (change p 132 none) else d16 (change p 132 none)) = d28 p
  rw [sub1808, sub1797]
  rfl
theorem sub1810 (p : Pattern) : d256 (change p 132 none) = d28 p := by
  change d28 (change p 132 none) = d28 p
  exact sub1809 p
theorem sub1811 (p : Pattern) : d46 (change p 132 none) = d46 p := by
  change (if p 134 then d25 (change p 132 none) else d15 (change p 132 none)) = d46 p
  rw [sub1806, sub1796]
  rfl
theorem sub1812 (p : Pattern) : d47 (change p 132 none) = d47 p := by
  change (if p 133 then d46 (change p 132 none) else d15 (change p 132 none)) = d47 p
  rw [sub1811, sub1796]
  rfl
theorem sub1813 (p : Pattern) : d257 (change p 132 none) = d47 p := by
  change d47 (change p 132 none) = d47 p
  exact sub1812 p
theorem sub1814 (p : Pattern) : d52 (change p 132 none) = d52 p := by
  change (if p 139 then d2 (change p 132 none) else d8 (change p 132 none)) = d52 p
  rw [sub1782, sub1788]
  rfl
theorem sub1815 (p : Pattern) : d53 (change p 132 none) = d53 p := by
  change (if p 138 then d52 (change p 132 none) else d15 (change p 132 none)) = d53 p
  rw [sub1814, sub1796]
  rfl
theorem sub1816 (p : Pattern) : d54 (change p 132 none) = d54 p := by
  change (if p 139 then d2 (change p 132 none) else d20 (change p 132 none)) = d54 p
  rw [sub1782, sub1801]
  rfl
theorem sub1817 (p : Pattern) : d55 (change p 132 none) = d55 p := by
  change (if p 138 then d54 (change p 132 none) else d25 (change p 132 none)) = d55 p
  rw [sub1816, sub1806]
  rfl
theorem sub1818 (p : Pattern) : d56 (change p 132 none) = d56 p := by
  change (if p 134 then d55 (change p 132 none) else d53 (change p 132 none)) = d56 p
  rw [sub1817, sub1815]
  rfl
theorem sub1819 (p : Pattern) : d57 (change p 132 none) = d57 p := by
  change (if p 133 then d56 (change p 132 none) else d53 (change p 132 none)) = d57 p
  rw [sub1818, sub1815]
  rfl
theorem sub1820 (p : Pattern) : d258 (change p 132 none) = d57 p := by
  change d57 (change p 132 none) = d57 p
  exact sub1819 p
theorem sub1821 (p : Pattern) : d259 (change p 132 none) = d1223 p := by
  change (if p 113 then d258 (change p 132 none) else d257 (change p 132 none)) = d1223 p
  rw [sub1820, sub1813]
  rfl
theorem sub1822 (p : Pattern) : d260 (change p 132 none) = d1224 p := by
  change (if p 112 then d259 (change p 132 none) else d256 (change p 132 none)) = d1224 p
  rw [sub1821, sub1810]
  rfl
theorem sub1823 (p : Pattern) : d261 (change p 132 none) = d28 p := by
  change d28 (change p 132 none) = d28 p
  exact sub1809 p
theorem sub1824 (p : Pattern) : d262 (change p 132 none) = d28 p := by
  change (if p 113 then d261 (change p 132 none) else d256 (change p 132 none)) = d28 p
  rw [sub1823, sub1810]
  simp only [ite_self]
theorem sub1825 (p : Pattern) : d263 (change p 132 none) = d57 p := by
  change d57 (change p 132 none) = d57 p
  exact sub1819 p
theorem sub1826 (p : Pattern) : d264 (change p 132 none) = d1223 p := by
  change (if p 113 then d263 (change p 132 none) else d257 (change p 132 none)) = d1223 p
  rw [sub1825, sub1813]
  rfl
theorem sub1827 (p : Pattern) : d265 (change p 132 none) = d1224 p := by
  change (if p 112 then d264 (change p 132 none) else d262 (change p 132 none)) = d1224 p
  rw [sub1826, sub1824]
  rfl
theorem sub1828 (p : Pattern) : d266 (change p 132 none) = d1224 p := by
  change (if p 106 then d265 (change p 132 none) else d260 (change p 132 none)) = d1224 p
  rw [sub1827, sub1822]
  simp only [ite_self]
theorem sub1829 (p : Pattern) : d86 (change p 132 none) = d86 p := by
  change (if p 138 then d52 (change p 132 none) else d8 (change p 132 none)) = d86 p
  rw [sub1814, sub1788]
  rfl
theorem sub1830 (p : Pattern) : d87 (change p 132 none) = d87 p := by
  change (if p 138 then d54 (change p 132 none) else d20 (change p 132 none)) = d87 p
  rw [sub1816, sub1801]
  rfl
theorem sub1831 (p : Pattern) : d88 (change p 132 none) = d88 p := by
  change (if p 134 then d87 (change p 132 none) else d86 (change p 132 none)) = d88 p
  rw [sub1830, sub1829]
  rfl
theorem sub1832 (p : Pattern) : d89 (change p 132 none) = d89 p := by
  change (if p 133 then d88 (change p 132 none) else d86 (change p 132 none)) = d89 p
  rw [sub1831, sub1829]
  rfl
theorem sub1833 (p : Pattern) : d267 (change p 132 none) = d89 p := by
  change d89 (change p 132 none) = d89 p
  exact sub1832 p
theorem sub1834 (p : Pattern) : d268 (change p 132 none) = d1225 p := by
  change (if p 113 then d267 (change p 132 none) else d256 (change p 132 none)) = d1225 p
  rw [sub1833, sub1810]
  rfl
theorem sub1835 (p : Pattern) : d97 (change p 132 none) = d97 p := by
  change (if p 139 then d2 (change p 132 none) else d14 (change p 132 none)) = d97 p
  rw [sub1782, sub1795]
  rfl
theorem sub1836 (p : Pattern) : d98 (change p 132 none) = d98 p := by
  change (if p 138 then d97 (change p 132 none) else d14 (change p 132 none)) = d98 p
  rw [sub1835, sub1795]
  rfl
theorem sub1837 (p : Pattern) : d70 (change p 132 none) = d70 p := by
  change (if p 139 then d2 (change p 132 none) else d24 (change p 132 none)) = d70 p
  rw [sub1782, sub1805]
  rfl
theorem sub1838 (p : Pattern) : d71 (change p 132 none) = d71 p := by
  change (if p 138 then d70 (change p 132 none) else d24 (change p 132 none)) = d71 p
  rw [sub1837, sub1805]
  rfl
theorem sub1839 (p : Pattern) : d99 (change p 132 none) = d99 p := by
  change (if p 134 then d71 (change p 132 none) else d98 (change p 132 none)) = d99 p
  rw [sub1838, sub1836]
  rfl
theorem sub1840 (p : Pattern) : d100 (change p 132 none) = d100 p := by
  change (if p 133 then d99 (change p 132 none) else d98 (change p 132 none)) = d100 p
  rw [sub1839, sub1836]
  rfl
theorem sub1841 (p : Pattern) : d269 (change p 132 none) = d100 p := by
  change d100 (change p 132 none) = d100 p
  exact sub1840 p
theorem sub1842 (p : Pattern) : d270 (change p 132 none) = d100 p := by
  change d100 (change p 132 none) = d100 p
  exact sub1840 p
theorem sub1843 (p : Pattern) : d271 (change p 132 none) = d100 p := by
  change (if p 113 then d270 (change p 132 none) else d269 (change p 132 none)) = d100 p
  rw [sub1842, sub1841]
  simp only [ite_self]
theorem sub1844 (p : Pattern) : d272 (change p 132 none) = d1226 p := by
  change (if p 112 then d271 (change p 132 none) else d268 (change p 132 none)) = d1226 p
  rw [sub1843, sub1834]
  rfl
theorem sub1845 (p : Pattern) : d273 (change p 132 none) = d89 p := by
  change d89 (change p 132 none) = d89 p
  exact sub1832 p
theorem sub1846 (p : Pattern) : d274 (change p 132 none) = d1225 p := by
  change (if p 113 then d273 (change p 132 none) else d261 (change p 132 none)) = d1225 p
  rw [sub1845, sub1823]
  rfl
theorem sub1847 (p : Pattern) : d109 (change p 132 none) = d109 p := by
  change (if p 134 then d70 (change p 132 none) else d97 (change p 132 none)) = d109 p
  rw [sub1837, sub1835]
  rfl
theorem sub1848 (p : Pattern) : d110 (change p 132 none) = d110 p := by
  change (if p 133 then d109 (change p 132 none) else d97 (change p 132 none)) = d110 p
  rw [sub1847, sub1835]
  rfl
theorem sub1849 (p : Pattern) : d275 (change p 132 none) = d110 p := by
  change d110 (change p 132 none) = d110 p
  exact sub1848 p
theorem sub1850 (p : Pattern) : d276 (change p 132 none) = d1227 p := by
  change (if p 113 then d275 (change p 132 none) else d270 (change p 132 none)) = d1227 p
  rw [sub1849, sub1842]
  rfl
theorem sub1851 (p : Pattern) : d277 (change p 132 none) = d1228 p := by
  change (if p 112 then d276 (change p 132 none) else d274 (change p 132 none)) = d1228 p
  rw [sub1850, sub1846]
  rfl
theorem sub1852 (p : Pattern) : d278 (change p 132 none) = d1229 p := by
  change (if p 106 then d277 (change p 132 none) else d272 (change p 132 none)) = d1229 p
  rw [sub1851, sub1844]
  rfl
theorem sub1853 (p : Pattern) : d279 (change p 132 none) = d1230 p := by
  change (if p 86 then d278 (change p 132 none) else d266 (change p 132 none)) = d1230 p
  rw [sub1852, sub1828]
  rfl
theorem sub1854 (p : Pattern) : d280 (change p 132 none) = d28 p := by
  change d28 (change p 132 none) = d28 p
  exact sub1809 p
theorem sub1855 (p : Pattern) : d281 (change p 132 none) = d28 p := by
  change (if p 113 then d280 (change p 132 none) else d261 (change p 132 none)) = d28 p
  rw [sub1854, sub1823]
  simp only [ite_self]
theorem sub1856 (p : Pattern) : d282 (change p 132 none) = d47 p := by
  change d47 (change p 132 none) = d47 p
  exact sub1812 p
theorem sub1857 (p : Pattern) : d283 (change p 132 none) = d57 p := by
  change d57 (change p 132 none) = d57 p
  exact sub1819 p
theorem sub1858 (p : Pattern) : d284 (change p 132 none) = d1223 p := by
  change (if p 113 then d283 (change p 132 none) else d282 (change p 132 none)) = d1223 p
  rw [sub1857, sub1856]
  rfl
theorem sub1859 (p : Pattern) : d285 (change p 132 none) = d1224 p := by
  change (if p 112 then d284 (change p 132 none) else d281 (change p 132 none)) = d1224 p
  rw [sub1858, sub1855]
  rfl
theorem sub1860 (p : Pattern) : d286 (change p 132 none) = d1224 p := by
  change (if p 106 then d285 (change p 132 none) else d265 (change p 132 none)) = d1224 p
  rw [sub1859, sub1827]
  simp only [ite_self]
theorem sub1861 (p : Pattern) : d287 (change p 132 none) = d1231 p := by
  change (if p 113 then d283 (change p 132 none) else d280 (change p 132 none)) = d1231 p
  rw [sub1857, sub1854]
  rfl
theorem sub1862 (p : Pattern) : d288 (change p 132 none) = d1232 p := by
  change (if p 113 then d2 (change p 132 none) else d275 (change p 132 none)) = d1232 p
  rw [sub1782, sub1849]
  rfl
theorem sub1863 (p : Pattern) : d289 (change p 132 none) = d1233 p := by
  change (if p 112 then d288 (change p 132 none) else d287 (change p 132 none)) = d1233 p
  rw [sub1862, sub1861]
  rfl
theorem sub1864 (p : Pattern) : d290 (change p 132 none) = d1234 p := by
  change (if p 106 then d289 (change p 132 none) else d277 (change p 132 none)) = d1234 p
  rw [sub1863, sub1851]
  rfl
theorem sub1865 (p : Pattern) : d291 (change p 132 none) = d1235 p := by
  change (if p 86 then d290 (change p 132 none) else d286 (change p 132 none)) = d1235 p
  rw [sub1864, sub1860]
  rfl
theorem sub1866 (p : Pattern) : d292 (change p 132 none) = d1236 p := by
  change (if p 80 then d291 (change p 132 none) else d279 (change p 132 none)) = d1236 p
  rw [sub1865, sub1853]
  rfl
theorem sub1867 (p : Pattern) : d0 (change p 133 (some 132)) = d0 p := by
  rfl
theorem sub1868 (p : Pattern) : d2 (change p 133 (some 132)) = d2 p := by
  rfl
theorem sub1869 (p : Pattern) : d3 (change p 133 (some 132)) = d3 p := by
  change (if p 161 then d2 (change p 133 (some 132)) else d0 (change p 133 (some 132))) = d3 p
  rw [sub1868, sub1867]
  rfl
theorem sub1870 (p : Pattern) : d4 (change p 133 (some 132)) = d4 p := by
  change (if p 160 then d3 (change p 133 (some 132)) else d0 (change p 133 (some 132))) = d4 p
  rw [sub1869, sub1867]
  rfl
theorem sub1871 (p : Pattern) : d5 (change p 133 (some 132)) = d5 p := by
  change (if p 160 then d2 (change p 133 (some 132)) else d0 (change p 133 (some 132))) = d5 p
  rw [sub1868, sub1867]
  rfl
theorem sub1872 (p : Pattern) : d6 (change p 133 (some 132)) = d6 p := by
  change (if p 159 then d5 (change p 133 (some 132)) else d4 (change p 133 (some 132))) = d6 p
  rw [sub1871, sub1870]
  rfl
theorem sub1873 (p : Pattern) : d7 (change p 133 (some 132)) = d7 p := by
  change (if p 159 then d2 (change p 133 (some 132)) else d4 (change p 133 (some 132))) = d7 p
  rw [sub1868, sub1870]
  rfl
theorem sub1874 (p : Pattern) : d8 (change p 133 (some 132)) = d8 p := by
  change (if p 158 then d7 (change p 133 (some 132)) else d6 (change p 133 (some 132))) = d8 p
  rw [sub1873, sub1872]
  rfl
theorem sub1875 (p : Pattern) : d1 (change p 133 (some 132)) = d1 p := by
  rfl
theorem sub1876 (p : Pattern) : d9 (change p 133 (some 132)) = d9 p := by
  change (if p 161 then d2 (change p 133 (some 132)) else d1 (change p 133 (some 132))) = d9 p
  rw [sub1868, sub1875]
  rfl
theorem sub1877 (p : Pattern) : d10 (change p 133 (some 132)) = d10 p := by
  change (if p 160 then d9 (change p 133 (some 132)) else d1 (change p 133 (some 132))) = d10 p
  rw [sub1876, sub1875]
  rfl
theorem sub1878 (p : Pattern) : d11 (change p 133 (some 132)) = d11 p := by
  change (if p 160 then d2 (change p 133 (some 132)) else d1 (change p 133 (some 132))) = d11 p
  rw [sub1868, sub1875]
  rfl
theorem sub1879 (p : Pattern) : d12 (change p 133 (some 132)) = d12 p := by
  change (if p 159 then d11 (change p 133 (some 132)) else d10 (change p 133 (some 132))) = d12 p
  rw [sub1878, sub1877]
  rfl
theorem sub1880 (p : Pattern) : d13 (change p 133 (some 132)) = d13 p := by
  change (if p 159 then d2 (change p 133 (some 132)) else d10 (change p 133 (some 132))) = d13 p
  rw [sub1868, sub1877]
  rfl
theorem sub1881 (p : Pattern) : d14 (change p 133 (some 132)) = d14 p := by
  change (if p 158 then d13 (change p 133 (some 132)) else d12 (change p 133 (some 132))) = d14 p
  rw [sub1880, sub1879]
  rfl
theorem sub1882 (p : Pattern) : d15 (change p 133 (some 132)) = d15 p := by
  change (if p 139 then d14 (change p 133 (some 132)) else d8 (change p 133 (some 132))) = d15 p
  rw [sub1881, sub1874]
  rfl
theorem sub1883 (p : Pattern) : d16 (change p 133 (some 132)) = d16 p := by
  change (if p 138 then d15 (change p 133 (some 132)) else d8 (change p 133 (some 132))) = d16 p
  rw [sub1882, sub1874]
  rfl
theorem sub1884 (p : Pattern) : d293 (change p 133 (some 132)) = d16 p := by
  change d16 (change p 133 (some 132)) = d16 p
  exact sub1883 p
theorem sub1885 (p : Pattern) : d294 (change p 133 (some 132)) = d15 p := by
  change d15 (change p 133 (some 132)) = d15 p
  exact sub1882 p
theorem sub1886 (p : Pattern) : d52 (change p 133 (some 132)) = d52 p := by
  change (if p 139 then d2 (change p 133 (some 132)) else d8 (change p 133 (some 132))) = d52 p
  rw [sub1868, sub1874]
  rfl
theorem sub1887 (p : Pattern) : d53 (change p 133 (some 132)) = d53 p := by
  change (if p 138 then d52 (change p 133 (some 132)) else d15 (change p 133 (some 132))) = d53 p
  rw [sub1886, sub1882]
  rfl
theorem sub1888 (p : Pattern) : d295 (change p 133 (some 132)) = d53 p := by
  change d53 (change p 133 (some 132)) = d53 p
  exact sub1887 p
theorem sub1889 (p : Pattern) : d296 (change p 133 (some 132)) = d1152 p := by
  change (if p 113 then d295 (change p 133 (some 132)) else d294 (change p 133 (some 132))) = d1152 p
  rw [sub1888, sub1885]
  rfl
theorem sub1890 (p : Pattern) : d297 (change p 133 (some 132)) = d1153 p := by
  change (if p 112 then d296 (change p 133 (some 132)) else d293 (change p 133 (some 132))) = d1153 p
  rw [sub1889, sub1884]
  rfl
theorem sub1891 (p : Pattern) : d298 (change p 133 (some 132)) = d16 p := by
  change d16 (change p 133 (some 132)) = d16 p
  exact sub1883 p
theorem sub1892 (p : Pattern) : d299 (change p 133 (some 132)) = d16 p := by
  change d298 (change p 133 (some 132)) = d16 p
  exact sub1891 p
theorem sub1893 (p : Pattern) : d300 (change p 133 (some 132)) = d16 p := by
  change (if p 113 then d299 (change p 133 (some 132)) else d293 (change p 133 (some 132))) = d16 p
  rw [sub1892, sub1884]
  simp only [ite_self]
theorem sub1894 (p : Pattern) : d301 (change p 133 (some 132)) = d1153 p := by
  change (if p 112 then d296 (change p 133 (some 132)) else d300 (change p 133 (some 132))) = d1153 p
  rw [sub1889, sub1893]
  rfl
theorem sub1895 (p : Pattern) : d302 (change p 133 (some 132)) = d1153 p := by
  change (if p 106 then d301 (change p 133 (some 132)) else d297 (change p 133 (some 132))) = d1153 p
  rw [sub1894, sub1890]
  simp only [ite_self]
theorem sub1896 (p : Pattern) : d86 (change p 133 (some 132)) = d86 p := by
  change (if p 138 then d52 (change p 133 (some 132)) else d8 (change p 133 (some 132))) = d86 p
  rw [sub1886, sub1874]
  rfl
theorem sub1897 (p : Pattern) : d304 (change p 133 (some 132)) = d86 p := by
  change d86 (change p 133 (some 132)) = d86 p
  exact sub1896 p
theorem sub1898 (p : Pattern) : d305 (change p 133 (some 132)) = d86 p := by
  change d304 (change p 133 (some 132)) = d86 p
  exact sub1897 p
theorem sub1899 (p : Pattern) : d306 (change p 133 (some 132)) = d1154 p := by
  change (if p 113 then d305 (change p 133 (some 132)) else d293 (change p 133 (some 132))) = d1154 p
  rw [sub1898, sub1884]
  rfl
theorem sub1900 (p : Pattern) : d97 (change p 133 (some 132)) = d97 p := by
  change (if p 139 then d2 (change p 133 (some 132)) else d14 (change p 133 (some 132))) = d97 p
  rw [sub1868, sub1881]
  rfl
theorem sub1901 (p : Pattern) : d98 (change p 133 (some 132)) = d98 p := by
  change (if p 138 then d97 (change p 133 (some 132)) else d14 (change p 133 (some 132))) = d98 p
  rw [sub1900, sub1881]
  rfl
theorem sub1902 (p : Pattern) : d307 (change p 133 (some 132)) = d98 p := by
  change d98 (change p 133 (some 132)) = d98 p
  exact sub1901 p
theorem sub1903 (p : Pattern) : d308 (change p 133 (some 132)) = d1155 p := by
  change (if p 112 then d307 (change p 133 (some 132)) else d306 (change p 133 (some 132))) = d1155 p
  rw [sub1902, sub1899]
  rfl
theorem sub1904 (p : Pattern) : d309 (change p 133 (some 132)) = d86 p := by
  change d86 (change p 133 (some 132)) = d86 p
  exact sub1896 p
theorem sub1905 (p : Pattern) : d310 (change p 133 (some 132)) = d86 p := by
  change d309 (change p 133 (some 132)) = d86 p
  exact sub1904 p
theorem sub1906 (p : Pattern) : d311 (change p 133 (some 132)) = d1154 p := by
  change (if p 113 then d310 (change p 133 (some 132)) else d299 (change p 133 (some 132))) = d1154 p
  rw [sub1905, sub1892]
  rfl
theorem sub1907 (p : Pattern) : d312 (change p 133 (some 132)) = d97 p := by
  change d97 (change p 133 (some 132)) = d97 p
  exact sub1900 p
theorem sub1908 (p : Pattern) : d313 (change p 133 (some 132)) = d1156 p := by
  change (if p 113 then d312 (change p 133 (some 132)) else d307 (change p 133 (some 132))) = d1156 p
  rw [sub1907, sub1902]
  rfl
theorem sub1909 (p : Pattern) : d314 (change p 133 (some 132)) = d1157 p := by
  change (if p 112 then d313 (change p 133 (some 132)) else d311 (change p 133 (some 132))) = d1157 p
  rw [sub1908, sub1906]
  rfl
theorem sub1910 (p : Pattern) : d315 (change p 133 (some 132)) = d1158 p := by
  change (if p 106 then d314 (change p 133 (some 132)) else d308 (change p 133 (some 132))) = d1158 p
  rw [sub1909, sub1903]
  rfl
theorem sub1911 (p : Pattern) : d316 (change p 133 (some 132)) = d1159 p := by
  change (if p 86 then d315 (change p 133 (some 132)) else d302 (change p 133 (some 132))) = d1159 p
  rw [sub1910, sub1895]
  rfl
theorem sub1912 (p : Pattern) : d317 (change p 133 (some 132)) = d16 p := by
  change d16 (change p 133 (some 132)) = d16 p
  exact sub1883 p
theorem sub1913 (p : Pattern) : d318 (change p 133 (some 132)) = d16 p := by
  change d317 (change p 133 (some 132)) = d16 p
  exact sub1912 p
theorem sub1914 (p : Pattern) : d319 (change p 133 (some 132)) = d16 p := by
  change (if p 113 then d318 (change p 133 (some 132)) else d299 (change p 133 (some 132))) = d16 p
  rw [sub1913, sub1892]
  simp only [ite_self]
theorem sub1915 (p : Pattern) : d320 (change p 133 (some 132)) = d1153 p := by
  change (if p 112 then d296 (change p 133 (some 132)) else d319 (change p 133 (some 132))) = d1153 p
  rw [sub1889, sub1914]
  rfl
theorem sub1916 (p : Pattern) : d321 (change p 133 (some 132)) = d1153 p := by
  change (if p 106 then d320 (change p 133 (some 132)) else d301 (change p 133 (some 132))) = d1153 p
  rw [sub1915, sub1894]
  simp only [ite_self]
theorem sub1917 (p : Pattern) : d322 (change p 133 (some 132)) = d1160 p := by
  change (if p 113 then d295 (change p 133 (some 132)) else d318 (change p 133 (some 132))) = d1160 p
  rw [sub1888, sub1913]
  rfl
theorem sub1918 (p : Pattern) : d323 (change p 133 (some 132)) = d1161 p := by
  change (if p 113 then d2 (change p 133 (some 132)) else d312 (change p 133 (some 132))) = d1161 p
  rw [sub1868, sub1907]
  rfl
theorem sub1919 (p : Pattern) : d324 (change p 133 (some 132)) = d1162 p := by
  change (if p 112 then d323 (change p 133 (some 132)) else d322 (change p 133 (some 132))) = d1162 p
  rw [sub1918, sub1917]
  rfl
end NetHack.Sokoban32Refined
