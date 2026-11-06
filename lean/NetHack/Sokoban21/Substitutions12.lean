/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions11
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s1800 (pattern : Twelve) : d1278 (change pattern 12 10) = d8 pattern := by
  change (if pattern.i then d872 (change pattern 12 10) else d1275 (change pattern 12 10)) = d8 pattern
  rw [s1763, s1799]
  simp only [ite_self]
theorem s1801 (pattern : Twelve) : d1284 (change pattern 12 10) = d8 pattern := by
  change (if pattern.h then d872 (change pattern 12 10) else d1278 (change pattern 12 10)) = d8 pattern
  rw [s1763, s1800]
  simp only [ite_self]
theorem s1802 (pattern : Twelve) : d1293 (change pattern 12 10) = d2189 pattern := by
  change (if pattern.f then d1284 (change pattern 12 10) else d17 (change pattern 12 10)) = d2189 pattern
  rw [s1801, s1615]
  rfl
theorem s1803 (pattern : Twelve) : d1294 (change pattern 12 10) = d2190 pattern := by
  change (if pattern.f then d6 (change pattern 12 10) else d19 (change pattern 12 10)) = d2190 pattern
  rw [s1626, s1625]
  rfl
theorem s1804 (pattern : Twelve) : d1305 (change pattern 12 10) = d2191 pattern := by
  change (if pattern.e then d1294 (change pattern 12 10) else d1293 (change pattern 12 10)) = d2191 pattern
  rw [s1803, s1802]
  rfl
theorem s1805 (pattern : Twelve) : d1276 (change pattern 12 10) = d117 pattern := by
  change d117 (change pattern 12 10) = d117 pattern
  exact s1710 pattern
theorem s1806 (pattern : Twelve) : d1279 (change pattern 12 10) = d2192 pattern := by
  change (if pattern.i then d1276 (change pattern 12 10) else d1275 (change pattern 12 10)) = d2192 pattern
  rw [s1805, s1799]
  rfl
theorem s1807 (pattern : Twelve) : d1280 (change pattern 12 10) = d2193 pattern := by
  change (if pattern.i then d6 (change pattern 12 10) else d872 (change pattern 12 10)) = d2193 pattern
  rw [s1626, s1763]
  rfl
theorem s1808 (pattern : Twelve) : d1285 (change pattern 12 10) = d2194 pattern := by
  change (if pattern.h then d1280 (change pattern 12 10) else d1279 (change pattern 12 10)) = d2194 pattern
  rw [s1807, s1806]
  rfl
theorem s1809 (pattern : Twelve) : d1295 (change pattern 12 10) = d2195 pattern := by
  change (if pattern.f then d1285 (change pattern 12 10) else d827 (change pattern 12 10)) = d2195 pattern
  rw [s1808, s1739]
  rfl
theorem s1810 (pattern : Twelve) : d1286 (change pattern 12 10) = d2196 pattern := by
  change (if pattern.h then d29 (change pattern 12 10) else d817 (change pattern 12 10)) = d2196 pattern
  rw [s1627, s1732]
  rfl
theorem s1811 (pattern : Twelve) : d1296 (change pattern 12 10) = d2197 pattern := by
  change (if pattern.f then d6 (change pattern 12 10) else d1286 (change pattern 12 10)) = d2197 pattern
  rw [s1626, s1810]
  rfl
theorem s1812 (pattern : Twelve) : d1306 (change pattern 12 10) = d2198 pattern := by
  change (if pattern.e then d1296 (change pattern 12 10) else d1295 (change pattern 12 10)) = d2198 pattern
  rw [s1811, s1809]
  rfl
theorem s1813 (pattern : Twelve) : d1313 (change pattern 12 10) = d2199 pattern := by
  change (if pattern.j then d1306 (change pattern 12 10) else d1305 (change pattern 12 10)) = d2199 pattern
  rw [s1812, s1804]
  rfl
theorem s1814 (pattern : Twelve) : d1281 (change pattern 12 10) = d2192 pattern := by
  change (if pattern.i then d119 (change pattern 12 10) else d872 (change pattern 12 10)) = d2192 pattern
  rw [s1711, s1763]
  rfl
theorem s1815 (pattern : Twelve) : d1287 (change pattern 12 10) = d2192 pattern := by
  change (if pattern.h then d1281 (change pattern 12 10) else d1279 (change pattern 12 10)) = d2192 pattern
  rw [s1814, s1806]
  simp only [ite_self]
theorem s1816 (pattern : Twelve) : d1297 (change pattern 12 10) = d2200 pattern := by
  change (if pattern.f then d1287 (change pattern 12 10) else d34 (change pattern 12 10)) = d2200 pattern
  rw [s1815, s1647]
  rfl
theorem s1817 (pattern : Twelve) : d1298 (change pattern 12 10) = d2201 pattern := by
  change (if pattern.f then d6 (change pattern 12 10) else d817 (change pattern 12 10)) = d2201 pattern
  rw [s1626, s1732]
  rfl
theorem s1818 (pattern : Twelve) : d1307 (change pattern 12 10) = d2202 pattern := by
  change (if pattern.e then d1298 (change pattern 12 10) else d1297 (change pattern 12 10)) = d2202 pattern
  rw [s1817, s1816]
  rfl
theorem s1819 (pattern : Twelve) : d1277 (change pattern 12 10) = d14 pattern := by
  change d14 (change pattern 12 10) = d14 pattern
  exact s1638 pattern
theorem s1820 (pattern : Twelve) : d1282 (change pattern 12 10) = d2203 pattern := by
  change (if pattern.i then d1277 (change pattern 12 10) else d1276 (change pattern 12 10)) = d2203 pattern
  rw [s1819, s1805]
  rfl
theorem s1821 (pattern : Twelve) : d1288 (change pattern 12 10) = d2204 pattern := by
  change (if pattern.h then d125 (change pattern 12 10) else d1282 (change pattern 12 10)) = d2204 pattern
  rw [s1712, s1820]
  rfl
theorem s1822 (pattern : Twelve) : d1299 (change pattern 12 10) = d2205 pattern := by
  change (if pattern.f then d1288 (change pattern 12 10) else d830 (change pattern 12 10)) = d2205 pattern
  rw [s1821, s1752]
  rfl
theorem s1823 (pattern : Twelve) : d1289 (change pattern 12 10) = d2206 pattern := by
  change (if pattern.h then d42 (change pattern 12 10) else d821 (change pattern 12 10)) = d2206 pattern
  rw [s1679, s1753]
  rfl
theorem s1824 (pattern : Twelve) : d1300 (change pattern 12 10) = d2207 pattern := by
  change (if pattern.f then d6 (change pattern 12 10) else d1289 (change pattern 12 10)) = d2207 pattern
  rw [s1626, s1823]
  rfl
theorem s1825 (pattern : Twelve) : d1308 (change pattern 12 10) = d2208 pattern := by
  change (if pattern.e then d1300 (change pattern 12 10) else d1299 (change pattern 12 10)) = d2208 pattern
  rw [s1824, s1822]
  rfl
theorem s1826 (pattern : Twelve) : d1314 (change pattern 12 10) = d2209 pattern := by
  change (if pattern.j then d1308 (change pattern 12 10) else d1307 (change pattern 12 10)) = d2209 pattern
  rw [s1825, s1818]
  rfl
theorem s1827 (pattern : Twelve) : d1315 (change pattern 12 10) = d2210 pattern := by
  change (if pattern.j then d6 (change pattern 12 10) else d1306 (change pattern 12 10)) = d2210 pattern
  rw [s1626, s1812]
  rfl
theorem s1828 (pattern : Twelve) : d1319 (change pattern 12 10) = d2211 pattern := by
  change (if pattern.d then d1315 (change pattern 12 10) else d1314 (change pattern 12 10)) = d2211 pattern
  rw [s1827, s1826]
  rfl
theorem s1829 (pattern : Twelve) : d1321 (change pattern 12 10) = d2212 pattern := by
  change (if pattern.c then d1319 (change pattern 12 10) else d1313 (change pattern 12 10)) = d2212 pattern
  rw [s1828, s1813]
  rfl
theorem s1830 (pattern : Twelve) : d16 (change pattern 12 10) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 12 10) else d2 (change pattern 12 10)) = d16 pattern
  rw [s1632, s1619]
  rfl
theorem s1831 (pattern : Twelve) : d1324 (change pattern 12 10) = d16 pattern := by
  change d16 (change pattern 12 10) = d16 pattern
  exact s1830 pattern
theorem s1832 (pattern : Twelve) : d1325 (change pattern 12 10) = d2213 pattern := by
  change (if pattern.i then d1324 (change pattern 12 10) else d1275 (change pattern 12 10)) = d2213 pattern
  rw [s1831, s1799]
  rfl
theorem s1833 (pattern : Twelve) : d1326 (change pattern 12 10) = d2213 pattern := by
  change (if pattern.i then d1324 (change pattern 12 10) else d872 (change pattern 12 10)) = d2213 pattern
  rw [s1831, s1763]
  rfl
theorem s1834 (pattern : Twelve) : d1333 (change pattern 12 10) = d2213 pattern := by
  change (if pattern.h then d1326 (change pattern 12 10) else d1325 (change pattern 12 10)) = d2213 pattern
  rw [s1833, s1832]
  simp only [ite_self]
theorem s1835 (pattern : Twelve) : d1339 (change pattern 12 10) = d2214 pattern := by
  change (if pattern.f then d1333 (change pattern 12 10) else d17 (change pattern 12 10)) = d2214 pattern
  rw [s1834, s1615]
  rfl
theorem s1836 (pattern : Twelve) : d1345 (change pattern 12 10) = d2215 pattern := by
  change (if pattern.e then d1294 (change pattern 12 10) else d1339 (change pattern 12 10)) = d2215 pattern
  rw [s1803, s1835]
  rfl
theorem s1837 (pattern : Twelve) : d1327 (change pattern 12 10) = d2192 pattern := by
  change (if pattern.i then d119 (change pattern 12 10) else d1275 (change pattern 12 10)) = d2192 pattern
  rw [s1711, s1799]
  rfl
theorem s1838 (pattern : Twelve) : d1334 (change pattern 12 10) = d2194 pattern := by
  change (if pattern.h then d1280 (change pattern 12 10) else d1327 (change pattern 12 10)) = d2194 pattern
  rw [s1807, s1837]
  rfl
theorem s1839 (pattern : Twelve) : d1340 (change pattern 12 10) = d2195 pattern := by
  change (if pattern.f then d1334 (change pattern 12 10) else d827 (change pattern 12 10)) = d2195 pattern
  rw [s1838, s1739]
  rfl
theorem s1840 (pattern : Twelve) : d1346 (change pattern 12 10) = d2198 pattern := by
  change (if pattern.e then d1296 (change pattern 12 10) else d1340 (change pattern 12 10)) = d2198 pattern
  rw [s1811, s1839]
  rfl
theorem s1841 (pattern : Twelve) : d1349 (change pattern 12 10) = d2216 pattern := by
  change (if pattern.j then d1346 (change pattern 12 10) else d1345 (change pattern 12 10)) = d2216 pattern
  rw [s1840, s1836]
  rfl
theorem s1842 (pattern : Twelve) : d1328 (change pattern 12 10) = d2217 pattern := by
  change (if pattern.i then d1277 (change pattern 12 10) else d872 (change pattern 12 10)) = d2217 pattern
  rw [s1819, s1763]
  rfl
theorem s1843 (pattern : Twelve) : d1335 (change pattern 12 10) = d2218 pattern := by
  change (if pattern.h then d1328 (change pattern 12 10) else d1327 (change pattern 12 10)) = d2218 pattern
  rw [s1842, s1837]
  rfl
theorem s1844 (pattern : Twelve) : d1341 (change pattern 12 10) = d2219 pattern := by
  change (if pattern.f then d1335 (change pattern 12 10) else d34 (change pattern 12 10)) = d2219 pattern
  rw [s1843, s1647]
  rfl
theorem s1845 (pattern : Twelve) : d1329 (change pattern 12 10) = d2220 pattern := by
  change (if pattern.i then d20 (change pattern 12 10) else d19 (change pattern 12 10)) = d2220 pattern
  rw [s1634, s1625]
  rfl
theorem s1846 (pattern : Twelve) : d1336 (change pattern 12 10) = d2221 pattern := by
  change (if pattern.h then d1329 (change pattern 12 10) else d817 (change pattern 12 10)) = d2221 pattern
  rw [s1845, s1732]
  rfl
theorem s1847 (pattern : Twelve) : d1342 (change pattern 12 10) = d2222 pattern := by
  change (if pattern.f then d6 (change pattern 12 10) else d1336 (change pattern 12 10)) = d2222 pattern
  rw [s1626, s1846]
  rfl
theorem s1848 (pattern : Twelve) : d1347 (change pattern 12 10) = d2223 pattern := by
  change (if pattern.e then d1342 (change pattern 12 10) else d1341 (change pattern 12 10)) = d2223 pattern
  rw [s1847, s1844]
  rfl
theorem s1849 (pattern : Twelve) : d1330 (change pattern 12 10) = d2116 pattern := by
  change (if pattern.i then d6 (change pattern 12 10) else d1276 (change pattern 12 10)) = d2116 pattern
  rw [s1626, s1805]
  rfl
theorem s1850 (pattern : Twelve) : d1331 (change pattern 12 10) = d2148 pattern := by
  change (if pattern.i then d6 (change pattern 12 10) else d1277 (change pattern 12 10)) = d2148 pattern
  rw [s1626, s1819]
  rfl
theorem s1851 (pattern : Twelve) : d1337 (change pattern 12 10) = d2224 pattern := by
  change (if pattern.h then d1331 (change pattern 12 10) else d1330 (change pattern 12 10)) = d2224 pattern
  rw [s1850, s1849]
  rfl
theorem s1852 (pattern : Twelve) : d1343 (change pattern 12 10) = d2225 pattern := by
  change (if pattern.f then d1337 (change pattern 12 10) else d830 (change pattern 12 10)) = d2225 pattern
  rw [s1851, s1752]
  rfl
theorem s1853 (pattern : Twelve) : d1332 (change pattern 12 10) = d2088 pattern := by
  change (if pattern.i then d22 (change pattern 12 10) else d25 (change pattern 12 10)) = d2088 pattern
  rw [s1643, s1678]
  rfl
theorem s1854 (pattern : Twelve) : d1338 (change pattern 12 10) = d2226 pattern := by
  change (if pattern.h then d128 (change pattern 12 10) else d1332 (change pattern 12 10)) = d2226 pattern
  rw [s1719, s1853]
  rfl
theorem s1855 (pattern : Twelve) : d1344 (change pattern 12 10) = d2227 pattern := by
  change (if pattern.f then d6 (change pattern 12 10) else d1338 (change pattern 12 10)) = d2227 pattern
  rw [s1626, s1854]
  rfl
theorem s1856 (pattern : Twelve) : d1348 (change pattern 12 10) = d2228 pattern := by
  change (if pattern.e then d1344 (change pattern 12 10) else d1343 (change pattern 12 10)) = d2228 pattern
  rw [s1855, s1852]
  rfl
theorem s1857 (pattern : Twelve) : d1350 (change pattern 12 10) = d2229 pattern := by
  change (if pattern.j then d1348 (change pattern 12 10) else d1347 (change pattern 12 10)) = d2229 pattern
  rw [s1856, s1848]
  rfl
theorem s1858 (pattern : Twelve) : d1351 (change pattern 12 10) = d2210 pattern := by
  change (if pattern.j then d6 (change pattern 12 10) else d1346 (change pattern 12 10)) = d2210 pattern
  rw [s1626, s1840]
  rfl
theorem s1859 (pattern : Twelve) : d1352 (change pattern 12 10) = d2230 pattern := by
  change (if pattern.d then d1351 (change pattern 12 10) else d1350 (change pattern 12 10)) = d2230 pattern
  rw [s1858, s1857]
  rfl
theorem s1860 (pattern : Twelve) : d1353 (change pattern 12 10) = d2231 pattern := by
  change (if pattern.c then d1352 (change pattern 12 10) else d1349 (change pattern 12 10)) = d2231 pattern
  rw [s1859, s1841]
  rfl
theorem s1861 (pattern : Twelve) : d1354 (change pattern 12 10) = d2232 pattern := by
  change (if pattern.a then d1353 (change pattern 12 10) else d1321 (change pattern 12 10)) = d2232 pattern
  rw [s1860, s1829]
  rfl
theorem s1862 (pattern : Twelve) : d1649 (change pattern 12 10) = d2233 pattern := by
  change (if pattern.f then d1324 (change pattern 12 10) else d19 (change pattern 12 10)) = d2233 pattern
  rw [s1831, s1625]
  rfl
theorem s1863 (pattern : Twelve) : d1650 (change pattern 12 10) = d2234 pattern := by
  change (if pattern.f then d6 (change pattern 12 10) else d25 (change pattern 12 10)) = d2234 pattern
  rw [s1626, s1678]
  rfl
theorem s1864 (pattern : Twelve) : d1656 (change pattern 12 10) = d2235 pattern := by
  change (if pattern.e then d1650 (change pattern 12 10) else d1649 (change pattern 12 10)) = d2235 pattern
  rw [s1863, s1862]
  rfl
theorem s1865 (pattern : Twelve) : d1644 (change pattern 12 10) = d2236 pattern := by
  change (if pattern.i then d20 (change pattern 12 10) else d1324 (change pattern 12 10)) = d2236 pattern
  rw [s1634, s1831]
  rfl
theorem s1866 (pattern : Twelve) : d1645 (change pattern 12 10) = d2237 pattern := by
  change (if pattern.i then d6 (change pattern 12 10) else d1324 (change pattern 12 10)) = d2237 pattern
  rw [s1626, s1831]
  rfl
theorem s1867 (pattern : Twelve) : d1647 (change pattern 12 10) = d2238 pattern := by
  change (if pattern.h then d1645 (change pattern 12 10) else d1644 (change pattern 12 10)) = d2238 pattern
  rw [s1866, s1865]
  rfl
theorem s1868 (pattern : Twelve) : d1651 (change pattern 12 10) = d2239 pattern := by
  change (if pattern.f then d1647 (change pattern 12 10) else d1286 (change pattern 12 10)) = d2239 pattern
  rw [s1867, s1810]
  rfl
theorem s1869 (pattern : Twelve) : d1657 (change pattern 12 10) = d2240 pattern := by
  change (if pattern.e then d1300 (change pattern 12 10) else d1651 (change pattern 12 10)) = d2240 pattern
  rw [s1824, s1868]
  rfl
theorem s1870 (pattern : Twelve) : d1660 (change pattern 12 10) = d2241 pattern := by
  change (if pattern.j then d1657 (change pattern 12 10) else d1656 (change pattern 12 10)) = d2241 pattern
  rw [s1869, s1864]
  rfl
theorem s1871 (pattern : Twelve) : d1652 (change pattern 12 10) = d2242 pattern := by
  change (if pattern.f then d1644 (change pattern 12 10) else d817 (change pattern 12 10)) = d2242 pattern
  rw [s1865, s1732]
  rfl
theorem s1872 (pattern : Twelve) : d1653 (change pattern 12 10) = d2243 pattern := by
  change (if pattern.f then d6 (change pattern 12 10) else d821 (change pattern 12 10)) = d2243 pattern
  rw [s1626, s1753]
  rfl
theorem s1873 (pattern : Twelve) : d1658 (change pattern 12 10) = d2244 pattern := by
  change (if pattern.e then d1653 (change pattern 12 10) else d1652 (change pattern 12 10)) = d2244 pattern
  rw [s1872, s1871]
  rfl
theorem s1874 (pattern : Twelve) : d1646 (change pattern 12 10) = d2119 pattern := by
  change (if pattern.i then d22 (change pattern 12 10) else d20 (change pattern 12 10)) = d2119 pattern
  rw [s1643, s1634]
  rfl
theorem s1875 (pattern : Twelve) : d1648 (change pattern 12 10) = d2119 pattern := by
  change (if pattern.h then d128 (change pattern 12 10) else d1646 (change pattern 12 10)) = d2119 pattern
  rw [s1719, s1874]
  simp only [ite_self]
theorem s1876 (pattern : Twelve) : d1654 (change pattern 12 10) = d2245 pattern := by
  change (if pattern.f then d1648 (change pattern 12 10) else d1289 (change pattern 12 10)) = d2245 pattern
  rw [s1875, s1823]
  rfl
theorem s1877 (pattern : Twelve) : d1655 (change pattern 12 10) = d2246 pattern := by
  change (if pattern.f then d6 (change pattern 12 10) else d822 (change pattern 12 10)) = d2246 pattern
  rw [s1626, s1754]
  rfl
theorem s1878 (pattern : Twelve) : d1659 (change pattern 12 10) = d2247 pattern := by
  change (if pattern.e then d1655 (change pattern 12 10) else d1654 (change pattern 12 10)) = d2247 pattern
  rw [s1877, s1876]
  rfl
theorem s1879 (pattern : Twelve) : d1661 (change pattern 12 10) = d2248 pattern := by
  change (if pattern.j then d1659 (change pattern 12 10) else d1658 (change pattern 12 10)) = d2248 pattern
  rw [s1878, s1873]
  rfl
theorem s1880 (pattern : Twelve) : d1662 (change pattern 12 10) = d2249 pattern := by
  change (if pattern.j then d6 (change pattern 12 10) else d1657 (change pattern 12 10)) = d2249 pattern
  rw [s1626, s1869]
  rfl
theorem s1881 (pattern : Twelve) : d1663 (change pattern 12 10) = d2250 pattern := by
  change (if pattern.d then d1662 (change pattern 12 10) else d1661 (change pattern 12 10)) = d2250 pattern
  rw [s1880, s1879]
  rfl
theorem s1882 (pattern : Twelve) : d1664 (change pattern 12 10) = d2251 pattern := by
  change (if pattern.c then d1663 (change pattern 12 10) else d1660 (change pattern 12 10)) = d2251 pattern
  rw [s1881, s1870]
  rfl
theorem s1883 (pattern : Twelve) : d1668 (change pattern 12 10) = d2252 pattern := by
  change (if pattern.f then d1644 (change pattern 12 10) else d19 (change pattern 12 10)) = d2252 pattern
  rw [s1865, s1625]
  rfl
theorem s1884 (pattern : Twelve) : d1671 (change pattern 12 10) = d2253 pattern := by
  change (if pattern.e then d1650 (change pattern 12 10) else d1668 (change pattern 12 10)) = d2253 pattern
  rw [s1863, s1883]
  rfl
theorem s1885 (pattern : Twelve) : d1674 (change pattern 12 10) = d2254 pattern := by
  change (if pattern.j then d1657 (change pattern 12 10) else d1671 (change pattern 12 10)) = d2254 pattern
  rw [s1869, s1884]
  rfl
theorem s1886 (pattern : Twelve) : d1665 (change pattern 12 10) = d2237 pattern := by
  change (if pattern.i then d22 (change pattern 12 10) else d1324 (change pattern 12 10)) = d2237 pattern
  rw [s1643, s1831]
  rfl
theorem s1887 (pattern : Twelve) : d1666 (change pattern 12 10) = d2238 pattern := by
  change (if pattern.h then d1665 (change pattern 12 10) else d1644 (change pattern 12 10)) = d2238 pattern
  rw [s1886, s1865]
  rfl
theorem s1888 (pattern : Twelve) : d1669 (change pattern 12 10) = d2255 pattern := by
  change (if pattern.f then d1666 (change pattern 12 10) else d817 (change pattern 12 10)) = d2255 pattern
  rw [s1887, s1732]
  rfl
theorem s1889 (pattern : Twelve) : d1672 (change pattern 12 10) = d2256 pattern := by
  change (if pattern.e then d1300 (change pattern 12 10) else d1669 (change pattern 12 10)) = d2256 pattern
  rw [s1824, s1888]
  rfl
theorem s1890 (pattern : Twelve) : d183 (change pattern 12 10) = d6 pattern := by
  change (if pattern.i then d6 (change pattern 12 10) else d22 (change pattern 12 10)) = d6 pattern
  rw [s1626, s1643]
  simp only [ite_self]
theorem s1891 (pattern : Twelve) : d1667 (change pattern 12 10) = d2257 pattern := by
  change (if pattern.h then d183 (change pattern 12 10) else d128 (change pattern 12 10)) = d2257 pattern
  rw [s1890, s1719]
  rfl
theorem s1892 (pattern : Twelve) : d1670 (change pattern 12 10) = d2258 pattern := by
  change (if pattern.f then d1667 (change pattern 12 10) else d1289 (change pattern 12 10)) = d2258 pattern
  rw [s1891, s1823]
  rfl
theorem s1893 (pattern : Twelve) : d1252 (change pattern 12 10) = d2259 pattern := by
  change (if pattern.h then d6 (change pattern 12 10) else d822 (change pattern 12 10)) = d2259 pattern
  rw [s1626, s1754]
  rfl
theorem s1894 (pattern : Twelve) : d1626 (change pattern 12 10) = d2260 pattern := by
  change (if pattern.f then d6 (change pattern 12 10) else d1252 (change pattern 12 10)) = d2260 pattern
  rw [s1626, s1893]
  rfl
theorem s1895 (pattern : Twelve) : d1673 (change pattern 12 10) = d2261 pattern := by
  change (if pattern.e then d1626 (change pattern 12 10) else d1670 (change pattern 12 10)) = d2261 pattern
  rw [s1894, s1892]
  rfl
theorem s1896 (pattern : Twelve) : d1675 (change pattern 12 10) = d2262 pattern := by
  change (if pattern.j then d1673 (change pattern 12 10) else d1672 (change pattern 12 10)) = d2262 pattern
  rw [s1895, s1889]
  rfl
theorem s1897 (pattern : Twelve) : d1676 (change pattern 12 10) = d2263 pattern := by
  change (if pattern.d then d1662 (change pattern 12 10) else d1675 (change pattern 12 10)) = d2263 pattern
  rw [s1880, s1896]
  rfl
theorem s1898 (pattern : Twelve) : d1677 (change pattern 12 10) = d2264 pattern := by
  change (if pattern.c then d1676 (change pattern 12 10) else d1674 (change pattern 12 10)) = d2264 pattern
  rw [s1897, s1885]
  rfl
theorem s1899 (pattern : Twelve) : d1678 (change pattern 12 10) = d2265 pattern := by
  change (if pattern.a then d1677 (change pattern 12 10) else d1664 (change pattern 12 10)) = d2265 pattern
  rw [s1898, s1882]
  rfl
theorem s1900 (pattern : Twelve) : d0 (change pattern 2 3) = d0 pattern := by
  rfl
theorem s1901 (pattern : Twelve) : d1 (change pattern 2 3) = d1 pattern := by
  rfl
theorem s1902 (pattern : Twelve) : d26 (change pattern 2 3) = d26 pattern := by
  change (if pattern.i then d1 (change pattern 2 3) else d0 (change pattern 2 3)) = d26 pattern
  rw [s1901, s1900]
  rfl
theorem s1903 (pattern : Twelve) : d7 (change pattern 2 3) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 2 3) else d0 (change pattern 2 3)) = d7 pattern
  rw [s1901, s1900]
  rfl
theorem s1904 (pattern : Twelve) : d17 (change pattern 2 3) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 2 3) else d0 (change pattern 2 3)) = d17 pattern
  rw [s1903, s1900]
  rfl
theorem s1905 (pattern : Twelve) : d27 (change pattern 2 3) = d27 pattern := by
  change (if pattern.i then d1 (change pattern 2 3) else d17 (change pattern 2 3)) = d27 pattern
  rw [s1901, s1904]
  rfl
theorem s1906 (pattern : Twelve) : d50 (change pattern 2 3) = d50 pattern := by
  change (if pattern.h then d27 (change pattern 2 3) else d26 (change pattern 2 3)) = d50 pattern
  rw [s1905, s1902]
  rfl
theorem s1907 (pattern : Twelve) : d72 (change pattern 2 3) = d72 pattern := by
  change (if pattern.f then d50 (change pattern 2 3) else d0 (change pattern 2 3)) = d72 pattern
  rw [s1906, s1900]
  rfl
theorem s1908 (pattern : Twelve) : d2 (change pattern 2 3) = d2 pattern := by
  rfl
theorem s1909 (pattern : Twelve) : d3 (change pattern 2 3) = d3 pattern := by
  rfl
theorem s1910 (pattern : Twelve) : d9 (change pattern 2 3) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 2 3) else d2 (change pattern 2 3)) = d9 pattern
  rw [s1909, s1908]
  rfl
theorem s1911 (pattern : Twelve) : d23 (change pattern 2 3) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 2 3) else d2 (change pattern 2 3)) = d23 pattern
  rw [s1910, s1908]
  rfl
theorem s1912 (pattern : Twelve) : d34 (change pattern 2 3) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 2 3) else d17 (change pattern 2 3)) = d34 pattern
  rw [s1911, s1904]
  rfl
theorem s1913 (pattern : Twelve) : d10 (change pattern 2 3) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 2 3) else d0 (change pattern 2 3)) = d10 pattern
  rw [s1908, s1900]
  rfl
theorem s1914 (pattern : Twelve) : d11 (change pattern 2 3) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 2 3) else d1 (change pattern 2 3)) = d11 pattern
  rw [s1909, s1901]
  rfl
theorem s1915 (pattern : Twelve) : d19 (change pattern 2 3) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 2 3) else d10 (change pattern 2 3)) = d19 pattern
  rw [s1914, s1913]
  rfl
theorem s1916 (pattern : Twelve) : d6 (change pattern 2 3) = d6 pattern := by
  rfl
theorem s1917 (pattern : Twelve) : d29 (change pattern 2 3) = d29 pattern := by
  change (if pattern.i then d6 (change pattern 2 3) else d19 (change pattern 2 3)) = d29 pattern
  rw [s1916, s1915]
  rfl
theorem s1918 (pattern : Twelve) : d55 (change pattern 2 3) = d55 pattern := by
  change (if pattern.h then d29 (change pattern 2 3) else d34 (change pattern 2 3)) = d55 pattern
  rw [s1917, s1912]
  rfl
theorem s1919 (pattern : Twelve) : d76 (change pattern 2 3) = d76 pattern := by
  change (if pattern.f then d55 (change pattern 2 3) else d0 (change pattern 2 3)) = d76 pattern
  rw [s1918, s1900]
  rfl
theorem s1920 (pattern : Twelve) : d93 (change pattern 2 3) = d93 pattern := by
  change (if pattern.e then d76 (change pattern 2 3) else d72 (change pattern 2 3)) = d93 pattern
  rw [s1919, s1907]
  rfl
theorem s1921 (pattern : Twelve) : d30 (change pattern 2 3) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 2 3) else d0 (change pattern 2 3)) = d30 pattern
  rw [s1908, s1900]
  rfl
theorem s1922 (pattern : Twelve) : d35 (change pattern 2 3) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 2 3) else d0 (change pattern 2 3)) = d35 pattern
  rw [s1916, s1900]
  rfl
theorem s1923 (pattern : Twelve) : d56 (change pattern 2 3) = d56 pattern := by
  change (if pattern.h then d35 (change pattern 2 3) else d30 (change pattern 2 3)) = d56 pattern
  rw [s1922, s1921]
  rfl
theorem s1924 (pattern : Twelve) : d36 (change pattern 2 3) = d36 pattern := by
  change (if pattern.i then d6 (change pattern 2 3) else d17 (change pattern 2 3)) = d36 pattern
  rw [s1916, s1904]
  rfl
theorem s1925 (pattern : Twelve) : d57 (change pattern 2 3) = d57 pattern := by
  change (if pattern.h then d36 (change pattern 2 3) else d30 (change pattern 2 3)) = d57 pattern
  rw [s1924, s1921]
  rfl
theorem s1926 (pattern : Twelve) : d77 (change pattern 2 3) = d77 pattern := by
  change (if pattern.f then d57 (change pattern 2 3) else d56 (change pattern 2 3)) = d77 pattern
  rw [s1925, s1923]
  rfl
theorem s1927 (pattern : Twelve) : d78 (change pattern 2 3) = d78 pattern := by
  change (if pattern.f then d55 (change pattern 2 3) else d56 (change pattern 2 3)) = d78 pattern
  rw [s1918, s1923]
  rfl
theorem s1928 (pattern : Twelve) : d94 (change pattern 2 3) = d94 pattern := by
  change (if pattern.e then d78 (change pattern 2 3) else d77 (change pattern 2 3)) = d94 pattern
  rw [s1927, s1926]
  rfl
theorem s1929 (pattern : Twelve) : d103 (change pattern 2 3) = d103 pattern := by
  change (if pattern.j then d94 (change pattern 2 3) else d93 (change pattern 2 3)) = d103 pattern
  rw [s1928, s1920]
  rfl
theorem s1930 (pattern : Twelve) : d110 (change pattern 2 3) = d103 pattern := by
  change d103 (change pattern 2 3) = d103 pattern
  exact s1929 pattern
theorem s1931 (pattern : Twelve) : d345 (change pattern 2 3) = d103 pattern := by
  change d110 (change pattern 2 3) = d103 pattern
  exact s1930 pattern
theorem s1932 (pattern : Twelve) : d80 (change pattern 2 3) = d80 pattern := by
  change (if pattern.f then d55 (change pattern 2 3) else d30 (change pattern 2 3)) = d80 pattern
  rw [s1918, s1921]
  rfl
theorem s1933 (pattern : Twelve) : d97 (change pattern 2 3) = d97 pattern := by
  change (if pattern.e then d80 (change pattern 2 3) else d72 (change pattern 2 3)) = d97 pattern
  rw [s1932, s1907]
  rfl
theorem s1934 (pattern : Twelve) : d45 (change pattern 2 3) = d45 pattern := by
  change (if pattern.i then d6 (change pattern 2 3) else d1 (change pattern 2 3)) = d45 pattern
  rw [s1916, s1901]
  rfl
theorem s1935 (pattern : Twelve) : d65 (change pattern 2 3) = d65 pattern := by
  change (if pattern.h then d45 (change pattern 2 3) else d30 (change pattern 2 3)) = d65 pattern
  rw [s1934, s1921]
  rfl
theorem s1936 (pattern : Twelve) : d85 (change pattern 2 3) = d85 pattern := by
  change (if pattern.f then d65 (change pattern 2 3) else d56 (change pattern 2 3)) = d85 pattern
  rw [s1935, s1923]
  rfl
theorem s1937 (pattern : Twelve) : d39 (change pattern 2 3) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 2 3) else d2 (change pattern 2 3)) = d39 pattern
  rw [s1916, s1908]
  rfl
theorem s1938 (pattern : Twelve) : d66 (change pattern 2 3) = d66 pattern := by
  change (if pattern.h then d39 (change pattern 2 3) else d30 (change pattern 2 3)) = d66 pattern
  rw [s1937, s1921]
  rfl
theorem s1939 (pattern : Twelve) : d40 (change pattern 2 3) = d40 pattern := by
  change (if pattern.i then d6 (change pattern 2 3) else d23 (change pattern 2 3)) = d40 pattern
  rw [s1916, s1911]
  rfl
theorem s1940 (pattern : Twelve) : d64 (change pattern 2 3) = d64 pattern := by
  change (if pattern.h then d40 (change pattern 2 3) else d34 (change pattern 2 3)) = d64 pattern
  rw [s1939, s1912]
  rfl
theorem s1941 (pattern : Twelve) : d86 (change pattern 2 3) = d86 pattern := by
  change (if pattern.f then d64 (change pattern 2 3) else d66 (change pattern 2 3)) = d86 pattern
  rw [s1940, s1938]
  rfl
theorem s1942 (pattern : Twelve) : d99 (change pattern 2 3) = d99 pattern := by
  change (if pattern.e then d86 (change pattern 2 3) else d85 (change pattern 2 3)) = d99 pattern
  rw [s1941, s1936]
  rfl
theorem s1943 (pattern : Twelve) : d107 (change pattern 2 3) = d107 pattern := by
  change (if pattern.j then d99 (change pattern 2 3) else d97 (change pattern 2 3)) = d107 pattern
  rw [s1942, s1933]
  rfl
theorem s1944 (pattern : Twelve) : d112 (change pattern 2 3) = d107 pattern := by
  change d107 (change pattern 2 3) = d107 pattern
  exact s1943 pattern
theorem s1945 (pattern : Twelve) : d346 (change pattern 2 3) = d107 pattern := by
  change d112 (change pattern 2 3) = d107 pattern
  exact s1944 pattern
theorem s1946 (pattern : Twelve) : d348 (change pattern 2 3) = d2267 pattern := by
  change (if pattern.g then d346 (change pattern 2 3) else d345 (change pattern 2 3)) = d2267 pattern
  rw [s1945, s1931]
  rfl
theorem s1947 (pattern : Twelve) : d347 (change pattern 2 3) = d103 pattern := by
  change d110 (change pattern 2 3) = d103 pattern
  exact s1930 pattern
theorem s1948 (pattern : Twelve) : d349 (change pattern 2 3) = d2267 pattern := by
  change (if pattern.g then d346 (change pattern 2 3) else d347 (change pattern 2 3)) = d2267 pattern
  rw [s1945, s1947]
  rfl
theorem s1949 (pattern : Twelve) : d350 (change pattern 2 3) = d2267 pattern := by
  change (if pattern.b then d349 (change pattern 2 3) else d348 (change pattern 2 3)) = d2267 pattern
  rw [s1948, s1946]
  simp only [ite_self]
end NetHack.Sokoban21.Diagram
