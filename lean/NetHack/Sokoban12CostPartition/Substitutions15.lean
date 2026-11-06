/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions14
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub1800 (p : Pattern) : d126 (change p 158 (some 132)) = d126 p := by
  change (if p 186 then d125 (change p 158 (some 132)) else d11 (change p 158 (some 132))) = d126 p
  rw [sub1799, sub1780]
  rfl
theorem sub1801 (p : Pattern) : d127 (change p 158 (some 132)) = d127 p := by
  change (if p 168 then d126 (change p 158 (some 132)) else d120 (change p 158 (some 132))) = d127 p
  rw [sub1800, sub1793]
  rfl
theorem sub1802 (p : Pattern) : d128 (change p 158 (some 132)) = d128 p := by
  change (if p 160 then d65 (change p 158 (some 132)) else d127 (change p 158 (some 132))) = d128 p
  rw [sub1797, sub1801]
  rfl
theorem sub1803 (p : Pattern) : d129 (change p 158 (some 132)) = d129 p := by
  change (if p 159 then d128 (change p 158 (some 132)) else d109 (change p 158 (some 132))) = d129 p
  rw [sub1802, sub1798]
  rfl
theorem sub1804 (p : Pattern) : d240 (change p 158 (some 132)) = d129 p := by
  change d129 (change p 158 (some 132)) = d129 p
  exact sub1803 p
theorem sub1805 (p : Pattern) : d241 (change p 158 (some 132)) = d775 p := by
  change (if p 141 then d240 (change p 158 (some 132)) else d181 (change p 158 (some 132))) = d775 p
  rw [sub1804, sub1796]
  rfl
theorem sub1806 (p : Pattern) : d242 (change p 158 (some 132)) = d776 p := by
  change (if p 134 then d241 (change p 158 (some 132)) else d70 (change p 158 (some 132))) = d776 p
  rw [sub1805, sub1790]
  rfl
theorem sub1807 (p : Pattern) : d66 (change p 158 (some 132)) = d66 p := by
  change (if p 141 then d65 (change p 158 (some 132)) else d55 (change p 158 (some 132))) = d66 p
  rw [sub1797, sub1771]
  rfl
theorem sub1808 (p : Pattern) : d244 (change p 158 (some 132)) = d778 p := by
  change (if p 133 then d66 (change p 158 (some 132)) else d242 (change p 158 (some 132))) = d778 p
  rw [sub1807, sub1806]
  rfl
theorem sub1809 (p : Pattern) : d316 (change p 158 (some 132)) = d778 p := by
  change d244 (change p 158 (some 132)) = d778 p
  exact sub1808 p
theorem sub1810 (p : Pattern) : d137 (change p 158 (some 132)) = d137 p := by
  change (if p 186 then d55 (change p 158 (some 132)) else d119 (change p 158 (some 132))) = d137 p
  rw [sub1771, sub1792]
  rfl
theorem sub1811 (p : Pattern) : d139 (change p 158 (some 132)) = d139 p := by
  change (if p 160 then d137 (change p 158 (some 132)) else d120 (change p 158 (some 132))) = d139 p
  rw [sub1810, sub1793]
  rfl
theorem sub1812 (p : Pattern) : d153 (change p 158 (some 132)) = d153 p := by
  change (if p 159 then d139 (change p 158 (some 132)) else d57 (change p 158 (some 132))) = d153 p
  rw [sub1811, sub1773]
  rfl
theorem sub1813 (p : Pattern) : d191 (change p 158 (some 132)) = d153 p := by
  change d153 (change p 158 (some 132)) = d153 p
  exact sub1812 p
theorem sub1814 (p : Pattern) : d143 (change p 158 (some 132)) = d143 p := by
  change (if p 186 then d60 (change p 158 (some 132)) else d125 (change p 158 (some 132))) = d143 p
  rw [sub1785, sub1799]
  rfl
theorem sub1815 (p : Pattern) : d144 (change p 158 (some 132)) = d144 p := by
  change (if p 168 then d143 (change p 158 (some 132)) else d137 (change p 158 (some 132))) = d144 p
  rw [sub1814, sub1810]
  rfl
theorem sub1816 (p : Pattern) : d146 (change p 158 (some 132)) = d146 p := by
  change (if p 160 then d144 (change p 158 (some 132)) else d127 (change p 158 (some 132))) = d146 p
  rw [sub1815, sub1801]
  rfl
theorem sub1817 (p : Pattern) : d155 (change p 158 (some 132)) = d155 p := by
  change (if p 159 then d146 (change p 158 (some 132)) else d63 (change p 158 (some 132))) = d155 p
  rw [sub1816, sub1788]
  rfl
theorem sub1818 (p : Pattern) : d253 (change p 158 (some 132)) = d155 p := by
  change d155 (change p 158 (some 132)) = d155 p
  exact sub1817 p
theorem sub1819 (p : Pattern) : d254 (change p 158 (some 132)) = d783 p := by
  change (if p 141 then d253 (change p 158 (some 132)) else d191 (change p 158 (some 132))) = d783 p
  rw [sub1818, sub1813]
  rfl
theorem sub1820 (p : Pattern) : d255 (change p 158 (some 132)) = d784 p := by
  change (if p 134 then d66 (change p 158 (some 132)) else d254 (change p 158 (some 132))) = d784 p
  rw [sub1807, sub1819]
  rfl
theorem sub1821 (p : Pattern) : d256 (change p 158 (some 132)) = d785 p := by
  change (if p 133 then d66 (change p 158 (some 132)) else d255 (change p 158 (some 132))) = d785 p
  rw [sub1807, sub1820]
  rfl
theorem sub1822 (p : Pattern) : d318 (change p 158 (some 132)) = d785 p := by
  change d256 (change p 158 (some 132)) = d785 p
  exact sub1821 p
theorem sub1823 (p : Pattern) : d319 (change p 158 (some 132)) = d1135 p := by
  change (if p 108 then d318 (change p 158 (some 132)) else d316 (change p 158 (some 132))) = d1135 p
  rw [sub1822, sub1809]
  rfl
theorem sub1824 (p : Pattern) : d0 (change p 10000 (some 186)) = d0 p := by
  rfl
theorem sub1825 (p : Pattern) : d2 (change p 10000 (some 186)) = d2 p := by
  rfl
theorem sub1826 (p : Pattern) : d6 (change p 10000 (some 186)) = d6 p := by
  change (if p 193 then d2 (change p 10000 (some 186)) else d0 (change p 10000 (some 186))) = d6 p
  rw [sub1825, sub1824]
  rfl
theorem sub1827 (p : Pattern) : d7 (change p 10000 (some 186)) = d7 p := by
  change (if p 192 then d6 (change p 10000 (some 186)) else d0 (change p 10000 (some 186))) = d7 p
  rw [sub1826, sub1824]
  rfl
theorem sub1828 (p : Pattern) : d4 (change p 10000 (some 186)) = d4 p := by
  rfl
theorem sub1829 (p : Pattern) : d54 (change p 10000 (some 186)) = d54 p := by
  change (if p 193 then d4 (change p 10000 (some 186)) else d2 (change p 10000 (some 186))) = d54 p
  rw [sub1828, sub1825]
  rfl
theorem sub1830 (p : Pattern) : d55 (change p 10000 (some 186)) = d55 p := by
  change (if p 192 then d54 (change p 10000 (some 186)) else d2 (change p 10000 (some 186))) = d55 p
  rw [sub1829, sub1825]
  rfl
theorem sub1831 (p : Pattern) : d56 (change p 10000 (some 186)) = d55 p := by
  change d55 (change p 10000 (some 186)) = d55 p
  exact sub1830 p
theorem sub1832 (p : Pattern) : d57 (change p 10000 (some 186)) = d106 p := by
  change (if p 160 then d56 (change p 10000 (some 186)) else d7 (change p 10000 (some 186))) = d106 p
  rw [sub1831, sub1827]
  rfl
theorem sub1833 (p : Pattern) : d1 (change p 10000 (some 186)) = d1 p := by
  rfl
theorem sub1834 (p : Pattern) : d8 (change p 10000 (some 186)) = d8 p := by
  change (if p 271 then d1 (change p 10000 (some 186)) else d0 (change p 10000 (some 186))) = d8 p
  rw [sub1833, sub1824]
  rfl
theorem sub1835 (p : Pattern) : d3 (change p 10000 (some 186)) = d3 p := by
  rfl
theorem sub1836 (p : Pattern) : d9 (change p 10000 (some 186)) = d9 p := by
  change (if p 271 then d3 (change p 10000 (some 186)) else d2 (change p 10000 (some 186))) = d9 p
  rw [sub1835, sub1825]
  rfl
theorem sub1837 (p : Pattern) : d10 (change p 10000 (some 186)) = d10 p := by
  change (if p 193 then d9 (change p 10000 (some 186)) else d8 (change p 10000 (some 186))) = d10 p
  rw [sub1836, sub1834]
  rfl
theorem sub1838 (p : Pattern) : d11 (change p 10000 (some 186)) = d11 p := by
  change (if p 192 then d10 (change p 10000 (some 186)) else d8 (change p 10000 (some 186))) = d11 p
  rw [sub1837, sub1834]
  rfl
theorem sub1839 (p : Pattern) : d12 (change p 10000 (some 186)) = d12 p := by
  change (if p 168 then d11 (change p 10000 (some 186)) else d7 (change p 10000 (some 186))) = d12 p
  rw [sub1838, sub1827]
  rfl
theorem sub1840 (p : Pattern) : d5 (change p 10000 (some 186)) = d5 p := by
  rfl
theorem sub1841 (p : Pattern) : d58 (change p 10000 (some 186)) = d58 p := by
  change (if p 271 then d5 (change p 10000 (some 186)) else d4 (change p 10000 (some 186))) = d58 p
  rw [sub1840, sub1828]
  rfl
theorem sub1842 (p : Pattern) : d59 (change p 10000 (some 186)) = d59 p := by
  change (if p 193 then d58 (change p 10000 (some 186)) else d9 (change p 10000 (some 186))) = d59 p
  rw [sub1841, sub1836]
  rfl
theorem sub1843 (p : Pattern) : d60 (change p 10000 (some 186)) = d60 p := by
  change (if p 192 then d59 (change p 10000 (some 186)) else d9 (change p 10000 (some 186))) = d60 p
  rw [sub1842, sub1836]
  rfl
theorem sub1844 (p : Pattern) : d61 (change p 10000 (some 186)) = d60 p := by
  change d60 (change p 10000 (some 186)) = d60 p
  exact sub1843 p
theorem sub1845 (p : Pattern) : d62 (change p 10000 (some 186)) = d65 p := by
  change (if p 168 then d61 (change p 10000 (some 186)) else d56 (change p 10000 (some 186))) = d65 p
  rw [sub1844, sub1831]
  rfl
theorem sub1846 (p : Pattern) : d63 (change p 10000 (some 186)) = d109 p := by
  change (if p 160 then d62 (change p 10000 (some 186)) else d12 (change p 10000 (some 186))) = d109 p
  rw [sub1845, sub1839]
  rfl
theorem sub1847 (p : Pattern) : d64 (change p 10000 (some 186)) = d227 p := by
  change (if p 141 then d63 (change p 10000 (some 186)) else d57 (change p 10000 (some 186))) = d227 p
  rw [sub1846, sub1832]
  rfl
theorem sub1848 (p : Pattern) : d106 (change p 10000 (some 186)) = d106 p := by
  change (if p 160 then d55 (change p 10000 (some 186)) else d7 (change p 10000 (some 186))) = d106 p
  rw [sub1830, sub1827]
  rfl
theorem sub1849 (p : Pattern) : d119 (change p 10000 (some 186)) = d119 p := by
  change (if p 187 then d55 (change p 10000 (some 186)) else d7 (change p 10000 (some 186))) = d119 p
  rw [sub1830, sub1827]
  rfl
theorem sub1850 (p : Pattern) : d120 (change p 10000 (some 186)) = d119 p := by
  change d119 (change p 10000 (some 186)) = d119 p
  exact sub1849 p
theorem sub1851 (p : Pattern) : d121 (change p 10000 (some 186)) = d505 p := by
  change (if p 160 then d55 (change p 10000 (some 186)) else d120 (change p 10000 (some 186))) = d505 p
  rw [sub1830, sub1850]
  rfl
theorem sub1852 (p : Pattern) : d122 (change p 10000 (some 186)) = d1136 p := by
  change (if p 159 then d121 (change p 10000 (some 186)) else d106 (change p 10000 (some 186))) = d1136 p
  rw [sub1851, sub1848]
  rfl
theorem sub1853 (p : Pattern) : d179 (change p 10000 (some 186)) = d1137 p := by
  change (if p 158 then d122 (change p 10000 (some 186)) else d106 (change p 10000 (some 186))) = d1137 p
  rw [sub1852, sub1848]
  rfl
theorem sub1854 (p : Pattern) : d65 (change p 10000 (some 186)) = d65 p := by
  change (if p 168 then d60 (change p 10000 (some 186)) else d55 (change p 10000 (some 186))) = d65 p
  rw [sub1843, sub1830]
  rfl
theorem sub1855 (p : Pattern) : d109 (change p 10000 (some 186)) = d109 p := by
  change (if p 160 then d65 (change p 10000 (some 186)) else d12 (change p 10000 (some 186))) = d109 p
  rw [sub1854, sub1839]
  rfl
theorem sub1856 (p : Pattern) : d125 (change p 10000 (some 186)) = d125 p := by
  change (if p 187 then d60 (change p 10000 (some 186)) else d11 (change p 10000 (some 186))) = d125 p
  rw [sub1843, sub1838]
  rfl
theorem sub1857 (p : Pattern) : d126 (change p 10000 (some 186)) = d125 p := by
  change d125 (change p 10000 (some 186)) = d125 p
  exact sub1856 p
theorem sub1858 (p : Pattern) : d127 (change p 10000 (some 186)) = d502 p := by
  change (if p 168 then d126 (change p 10000 (some 186)) else d120 (change p 10000 (some 186))) = d502 p
  rw [sub1857, sub1850]
  rfl
theorem sub1859 (p : Pattern) : d128 (change p 10000 (some 186)) = d506 p := by
  change (if p 160 then d65 (change p 10000 (some 186)) else d127 (change p 10000 (some 186))) = d506 p
  rw [sub1854, sub1858]
  rfl
theorem sub1860 (p : Pattern) : d129 (change p 10000 (some 186)) = d1138 p := by
  change (if p 159 then d128 (change p 10000 (some 186)) else d109 (change p 10000 (some 186))) = d1138 p
  rw [sub1859, sub1855]
  rfl
theorem sub1861 (p : Pattern) : d237 (change p 10000 (some 186)) = d1139 p := by
  change (if p 158 then d129 (change p 10000 (some 186)) else d109 (change p 10000 (some 186))) = d1139 p
  rw [sub1860, sub1855]
  rfl
theorem sub1862 (p : Pattern) : d238 (change p 10000 (some 186)) = d1140 p := by
  change (if p 141 then d237 (change p 10000 (some 186)) else d179 (change p 10000 (some 186))) = d1140 p
  rw [sub1861, sub1853]
  rfl
theorem sub1863 (p : Pattern) : d239 (change p 10000 (some 186)) = d1141 p := by
  change (if p 134 then d238 (change p 10000 (some 186)) else d64 (change p 10000 (some 186))) = d1141 p
  rw [sub1862, sub1847]
  rfl
theorem sub1864 (p : Pattern) : d68 (change p 10000 (some 186)) = d229 p := by
  change (if p 158 then d55 (change p 10000 (some 186)) else d57 (change p 10000 (some 186))) = d229 p
  rw [sub1830, sub1832]
  rfl
theorem sub1865 (p : Pattern) : d69 (change p 10000 (some 186)) = d230 p := by
  change (if p 158 then d65 (change p 10000 (some 186)) else d63 (change p 10000 (some 186))) = d230 p
  rw [sub1854, sub1846]
  rfl
theorem sub1866 (p : Pattern) : d70 (change p 10000 (some 186)) = d231 p := by
  change (if p 141 then d69 (change p 10000 (some 186)) else d68 (change p 10000 (some 186))) = d231 p
  rw [sub1865, sub1864]
  rfl
theorem sub1867 (p : Pattern) : d181 (change p 10000 (some 186)) = d1142 p := by
  change (if p 158 then d55 (change p 10000 (some 186)) else d122 (change p 10000 (some 186))) = d1142 p
  rw [sub1830, sub1852]
  rfl
theorem sub1868 (p : Pattern) : d240 (change p 10000 (some 186)) = d1143 p := by
  change (if p 158 then d65 (change p 10000 (some 186)) else d129 (change p 10000 (some 186))) = d1143 p
  rw [sub1854, sub1860]
  rfl
theorem sub1869 (p : Pattern) : d241 (change p 10000 (some 186)) = d1144 p := by
  change (if p 141 then d240 (change p 10000 (some 186)) else d181 (change p 10000 (some 186))) = d1144 p
  rw [sub1868, sub1867]
  rfl
theorem sub1870 (p : Pattern) : d242 (change p 10000 (some 186)) = d1145 p := by
  change (if p 134 then d241 (change p 10000 (some 186)) else d70 (change p 10000 (some 186))) = d1145 p
  rw [sub1869, sub1866]
  rfl
theorem sub1871 (p : Pattern) : d243 (change p 10000 (some 186)) = d1146 p := by
  change (if p 133 then d242 (change p 10000 (some 186)) else d239 (change p 10000 (some 186))) = d1146 p
  rw [sub1870, sub1863]
  rfl
theorem sub1872 (p : Pattern) : d66 (change p 10000 (some 186)) = d66 p := by
  change (if p 141 then d65 (change p 10000 (some 186)) else d55 (change p 10000 (some 186))) = d66 p
  rw [sub1854, sub1830]
  rfl
theorem sub1873 (p : Pattern) : d244 (change p 10000 (some 186)) = d1147 p := by
  change (if p 133 then d66 (change p 10000 (some 186)) else d242 (change p 10000 (some 186))) = d1147 p
  rw [sub1872, sub1870]
  rfl
theorem sub1874 (p : Pattern) : d245 (change p 10000 (some 186)) = d1148 p := by
  change (if p 132 then d244 (change p 10000 (some 186)) else d243 (change p 10000 (some 186))) = d1148 p
  rw [sub1873, sub1871]
  rfl
theorem sub1875 (p : Pattern) : d137 (change p 10000 (some 186)) = d55 p := by
  change d55 (change p 10000 (some 186)) = d55 p
  exact sub1830 p
theorem sub1876 (p : Pattern) : d139 (change p 10000 (some 186)) = d505 p := by
  change (if p 160 then d137 (change p 10000 (some 186)) else d120 (change p 10000 (some 186))) = d505 p
  rw [sub1875, sub1850]
  rfl
theorem sub1877 (p : Pattern) : d153 (change p 10000 (some 186)) = d1136 p := by
  change (if p 159 then d139 (change p 10000 (some 186)) else d57 (change p 10000 (some 186))) = d1136 p
  rw [sub1876, sub1832]
  rfl
theorem sub1878 (p : Pattern) : d186 (change p 10000 (some 186)) = d1137 p := by
  change (if p 158 then d153 (change p 10000 (some 186)) else d57 (change p 10000 (some 186))) = d1137 p
  rw [sub1877, sub1832]
  rfl
theorem sub1879 (p : Pattern) : d143 (change p 10000 (some 186)) = d60 p := by
  change d60 (change p 10000 (some 186)) = d60 p
  exact sub1843 p
theorem sub1880 (p : Pattern) : d144 (change p 10000 (some 186)) = d65 p := by
  change (if p 168 then d143 (change p 10000 (some 186)) else d137 (change p 10000 (some 186))) = d65 p
  rw [sub1879, sub1875]
  rfl
theorem sub1881 (p : Pattern) : d146 (change p 10000 (some 186)) = d506 p := by
  change (if p 160 then d144 (change p 10000 (some 186)) else d127 (change p 10000 (some 186))) = d506 p
  rw [sub1880, sub1858]
  rfl
theorem sub1882 (p : Pattern) : d155 (change p 10000 (some 186)) = d1138 p := by
  change (if p 159 then d146 (change p 10000 (some 186)) else d63 (change p 10000 (some 186))) = d1138 p
  rw [sub1881, sub1846]
  rfl
theorem sub1883 (p : Pattern) : d246 (change p 10000 (some 186)) = d1139 p := by
  change (if p 158 then d155 (change p 10000 (some 186)) else d63 (change p 10000 (some 186))) = d1139 p
  rw [sub1882, sub1846]
  rfl
theorem sub1884 (p : Pattern) : d247 (change p 10000 (some 186)) = d1140 p := by
  change (if p 141 then d246 (change p 10000 (some 186)) else d186 (change p 10000 (some 186))) = d1140 p
  rw [sub1883, sub1878]
  rfl
theorem sub1885 (p : Pattern) : d248 (change p 10000 (some 186)) = d1149 p := by
  change (if p 134 then d66 (change p 10000 (some 186)) else d247 (change p 10000 (some 186))) = d1149 p
  rw [sub1872, sub1884]
  rfl
theorem sub1886 (p : Pattern) : d138 (change p 10000 (some 186)) = d106 p := by
  change (if p 160 then d137 (change p 10000 (some 186)) else d7 (change p 10000 (some 186))) = d106 p
  rw [sub1875, sub1827]
  rfl
theorem sub1887 (p : Pattern) : d140 (change p 10000 (some 186)) = d1136 p := by
  change (if p 159 then d139 (change p 10000 (some 186)) else d138 (change p 10000 (some 186))) = d1136 p
  rw [sub1876, sub1886]
  rfl
theorem sub1888 (p : Pattern) : d188 (change p 10000 (some 186)) = d1142 p := by
  change (if p 158 then d55 (change p 10000 (some 186)) else d140 (change p 10000 (some 186))) = d1142 p
  rw [sub1830, sub1887]
  rfl
theorem sub1889 (p : Pattern) : d145 (change p 10000 (some 186)) = d109 p := by
  change (if p 160 then d144 (change p 10000 (some 186)) else d12 (change p 10000 (some 186))) = d109 p
  rw [sub1880, sub1839]
  rfl
theorem sub1890 (p : Pattern) : d147 (change p 10000 (some 186)) = d1138 p := by
  change (if p 159 then d146 (change p 10000 (some 186)) else d145 (change p 10000 (some 186))) = d1138 p
  rw [sub1881, sub1889]
  rfl
theorem sub1891 (p : Pattern) : d249 (change p 10000 (some 186)) = d1143 p := by
  change (if p 158 then d65 (change p 10000 (some 186)) else d147 (change p 10000 (some 186))) = d1143 p
  rw [sub1854, sub1890]
  rfl
theorem sub1892 (p : Pattern) : d250 (change p 10000 (some 186)) = d1144 p := by
  change (if p 141 then d249 (change p 10000 (some 186)) else d188 (change p 10000 (some 186))) = d1144 p
  rw [sub1891, sub1888]
  rfl
theorem sub1893 (p : Pattern) : d251 (change p 10000 (some 186)) = d1150 p := by
  change (if p 134 then d66 (change p 10000 (some 186)) else d250 (change p 10000 (some 186))) = d1150 p
  rw [sub1872, sub1892]
  rfl
theorem sub1894 (p : Pattern) : d252 (change p 10000 (some 186)) = d1151 p := by
  change (if p 133 then d251 (change p 10000 (some 186)) else d248 (change p 10000 (some 186))) = d1151 p
  rw [sub1893, sub1885]
  rfl
theorem sub1895 (p : Pattern) : d191 (change p 10000 (some 186)) = d1142 p := by
  change (if p 158 then d55 (change p 10000 (some 186)) else d153 (change p 10000 (some 186))) = d1142 p
  rw [sub1830, sub1877]
  rfl
theorem sub1896 (p : Pattern) : d253 (change p 10000 (some 186)) = d1143 p := by
  change (if p 158 then d65 (change p 10000 (some 186)) else d155 (change p 10000 (some 186))) = d1143 p
  rw [sub1854, sub1882]
  rfl
theorem sub1897 (p : Pattern) : d254 (change p 10000 (some 186)) = d1144 p := by
  change (if p 141 then d253 (change p 10000 (some 186)) else d191 (change p 10000 (some 186))) = d1144 p
  rw [sub1896, sub1895]
  rfl
theorem sub1898 (p : Pattern) : d255 (change p 10000 (some 186)) = d1150 p := by
  change (if p 134 then d66 (change p 10000 (some 186)) else d254 (change p 10000 (some 186))) = d1150 p
  rw [sub1872, sub1897]
  rfl
theorem sub1899 (p : Pattern) : d256 (change p 10000 (some 186)) = d1152 p := by
  change (if p 133 then d66 (change p 10000 (some 186)) else d255 (change p 10000 (some 186))) = d1152 p
  rw [sub1872, sub1898]
  rfl
theorem sub1900 (p : Pattern) : d257 (change p 10000 (some 186)) = d1153 p := by
  change (if p 132 then d256 (change p 10000 (some 186)) else d252 (change p 10000 (some 186))) = d1153 p
  rw [sub1899, sub1894]
  rfl
theorem sub1901 (p : Pattern) : d258 (change p 10000 (some 186)) = d1154 p := by
  change (if p 108 then d257 (change p 10000 (some 186)) else d245 (change p 10000 (some 186))) = d1154 p
  rw [sub1900, sub1874]
  rfl
theorem sub1902 (p : Pattern) : d0 (change p 159 (some 133)) = d0 p := by
  rfl
theorem sub1903 (p : Pattern) : d2 (change p 159 (some 133)) = d2 p := by
  rfl
theorem sub1904 (p : Pattern) : d6 (change p 159 (some 133)) = d6 p := by
  change (if p 193 then d2 (change p 159 (some 133)) else d0 (change p 159 (some 133))) = d6 p
  rw [sub1903, sub1902]
  rfl
theorem sub1905 (p : Pattern) : d7 (change p 159 (some 133)) = d7 p := by
  change (if p 192 then d6 (change p 159 (some 133)) else d0 (change p 159 (some 133))) = d7 p
  rw [sub1904, sub1902]
  rfl
theorem sub1906 (p : Pattern) : d4 (change p 159 (some 133)) = d4 p := by
  rfl
theorem sub1907 (p : Pattern) : d54 (change p 159 (some 133)) = d54 p := by
  change (if p 193 then d4 (change p 159 (some 133)) else d2 (change p 159 (some 133))) = d54 p
  rw [sub1906, sub1903]
  rfl
theorem sub1908 (p : Pattern) : d55 (change p 159 (some 133)) = d55 p := by
  change (if p 192 then d54 (change p 159 (some 133)) else d2 (change p 159 (some 133))) = d55 p
  rw [sub1907, sub1903]
  rfl
theorem sub1909 (p : Pattern) : d56 (change p 159 (some 133)) = d56 p := by
  change (if p 186 then d55 (change p 159 (some 133)) else d7 (change p 159 (some 133))) = d56 p
  rw [sub1908, sub1905]
  rfl
theorem sub1910 (p : Pattern) : d57 (change p 159 (some 133)) = d57 p := by
  change (if p 160 then d56 (change p 159 (some 133)) else d7 (change p 159 (some 133))) = d57 p
  rw [sub1909, sub1905]
  rfl
theorem sub1911 (p : Pattern) : d114 (change p 159 (some 133)) = d57 p := by
  change d57 (change p 159 (some 133)) = d57 p
  exact sub1910 p
theorem sub1912 (p : Pattern) : d338 (change p 159 (some 133)) = d68 p := by
  change (if p 158 then d55 (change p 159 (some 133)) else d114 (change p 159 (some 133))) = d68 p
  rw [sub1908, sub1911]
  rfl
theorem sub1913 (p : Pattern) : d1 (change p 159 (some 133)) = d1 p := by
  rfl
theorem sub1914 (p : Pattern) : d8 (change p 159 (some 133)) = d8 p := by
  change (if p 271 then d1 (change p 159 (some 133)) else d0 (change p 159 (some 133))) = d8 p
  rw [sub1913, sub1902]
  rfl
theorem sub1915 (p : Pattern) : d3 (change p 159 (some 133)) = d3 p := by
  rfl
theorem sub1916 (p : Pattern) : d9 (change p 159 (some 133)) = d9 p := by
  change (if p 271 then d3 (change p 159 (some 133)) else d2 (change p 159 (some 133))) = d9 p
  rw [sub1915, sub1903]
  rfl
theorem sub1917 (p : Pattern) : d10 (change p 159 (some 133)) = d10 p := by
  change (if p 193 then d9 (change p 159 (some 133)) else d8 (change p 159 (some 133))) = d10 p
  rw [sub1916, sub1914]
  rfl
theorem sub1918 (p : Pattern) : d11 (change p 159 (some 133)) = d11 p := by
  change (if p 192 then d10 (change p 159 (some 133)) else d8 (change p 159 (some 133))) = d11 p
  rw [sub1917, sub1914]
  rfl
theorem sub1919 (p : Pattern) : d12 (change p 159 (some 133)) = d12 p := by
  change (if p 168 then d11 (change p 159 (some 133)) else d7 (change p 159 (some 133))) = d12 p
  rw [sub1918, sub1905]
  rfl
end NetHack.Sokoban12CostPartition
