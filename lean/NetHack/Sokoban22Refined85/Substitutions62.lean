/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions61
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub7440 (p : Pattern) : d1822 (change p 204 none) = d5041 p := by
  change (if p 162 then d12 (change p 204 none) else d1821 (change p 204 none)) = d5041 p
  rw [sub7260, sub7439]
  rfl
theorem sub7441 (p : Pattern) : d1823 (change p 204 none) = d5042 p := by
  change (if p 161 then d12 (change p 204 none) else d1822 (change p 204 none)) = d5042 p
  rw [sub7260, sub7440]
  rfl
theorem sub7442 (p : Pattern) : d1824 (change p 204 none) = d5043 p := by
  change (if p 160 then d1823 (change p 204 none) else d1820 (change p 204 none)) = d5043 p
  rw [sub7441, sub7438]
  rfl
theorem sub7443 (p : Pattern) : d1825 (change p 204 none) = d5044 p := by
  change (if p 141 then d1824 (change p 204 none) else d1814 (change p 204 none)) = d5044 p
  rw [sub7442, sub7432]
  rfl
theorem sub7444 (p : Pattern) : d1826 (change p 204 none) = d5045 p := by
  change (if p 138 then d1825 (change p 204 none) else d1768 (change p 204 none)) = d5045 p
  rw [sub7443, sub7383]
  rfl
theorem sub7445 (p : Pattern) : d1827 (change p 204 none) = d5046 p := by
  change (if p 163 then d1756 (change p 204 none) else d1805 (change p 204 none)) = d5046 p
  rw [sub7368, sub7422]
  rfl
theorem sub7446 (p : Pattern) : d1828 (change p 204 none) = d5047 p := by
  change (if p 162 then d1757 (change p 204 none) else d1827 (change p 204 none)) = d5047 p
  rw [sub7369, sub7445]
  rfl
theorem sub7447 (p : Pattern) : d1829 (change p 204 none) = d5048 p := by
  change (if p 162 then d12 (change p 204 none) else d1757 (change p 204 none)) = d5048 p
  rw [sub7260, sub7369]
  rfl
theorem sub7448 (p : Pattern) : d1830 (change p 204 none) = d5049 p := by
  change (if p 161 then d1829 (change p 204 none) else d1828 (change p 204 none)) = d5049 p
  rw [sub7447, sub7446]
  rfl
theorem sub7449 (p : Pattern) : d1831 (change p 204 none) = d5050 p := by
  change (if p 161 then d12 (change p 204 none) else d1829 (change p 204 none)) = d5050 p
  rw [sub7260, sub7447]
  rfl
theorem sub7450 (p : Pattern) : d1832 (change p 204 none) = d5051 p := by
  change (if p 160 then d1831 (change p 204 none) else d1830 (change p 204 none)) = d5051 p
  rw [sub7449, sub7448]
  rfl
theorem sub7451 (p : Pattern) : d1833 (change p 204 none) = d5052 p := by
  change (if p 160 then d12 (change p 204 none) else d1831 (change p 204 none)) = d5052 p
  rw [sub7260, sub7449]
  rfl
theorem sub7452 (p : Pattern) : d1834 (change p 204 none) = d5053 p := by
  change (if p 141 then d1833 (change p 204 none) else d1832 (change p 204 none)) = d5053 p
  rw [sub7451, sub7450]
  rfl
theorem sub7453 (p : Pattern) : d1835 (change p 204 none) = d5054 p := by
  change (if p 138 then d1834 (change p 204 none) else d1825 (change p 204 none)) = d5054 p
  rw [sub7452, sub7443]
  rfl
theorem sub7454 (p : Pattern) : d1836 (change p 204 none) = d5055 p := by
  change (if p 116 then d1835 (change p 204 none) else d1826 (change p 204 none)) = d5055 p
  rw [sub7453, sub7444]
  rfl
theorem sub7455 (p : Pattern) : d1837 (change p 204 none) = d4986 p := by
  change (if p 163 then d1692 (change p 204 none) else d1690 (change p 204 none)) = d4986 p
  rw [sub7276, sub7273]
  simp only [ite_self]
theorem sub7456 (p : Pattern) : d1838 (change p 204 none) = d4989 p := by
  change (if p 162 then d1699 (change p 204 none) else d1837 (change p 204 none)) = d4989 p
  rw [sub7289, sub7455]
  rfl
theorem sub7457 (p : Pattern) : d1839 (change p 204 none) = d4993 p := by
  change (if p 161 then d1708 (change p 204 none) else d1838 (change p 204 none)) = d4993 p
  rw [sub7304, sub7456]
  rfl
theorem sub7458 (p : Pattern) : d1840 (change p 204 none) = d5001 p := by
  change (if p 160 then d1738 (change p 204 none) else d1839 (change p 204 none)) = d5001 p
  rw [sub7345, sub7457]
  rfl
theorem sub7459 (p : Pattern) : d1841 (change p 204 none) = d5003 p := by
  change (if p 163 then d1747 (change p 204 none) else d1692 (change p 204 none)) = d5003 p
  rw [sub7355, sub7276]
  rfl
theorem sub7460 (p : Pattern) : d1842 (change p 204 none) = d5005 p := by
  change (if p 162 then d1749 (change p 204 none) else d1841 (change p 204 none)) = d5005 p
  rw [sub7357, sub7459]
  rfl
theorem sub7461 (p : Pattern) : d1843 (change p 204 none) = d5011 p := by
  change (if p 161 then d1758 (change p 204 none) else d1842 (change p 204 none)) = d5011 p
  rw [sub7370, sub7460]
  rfl
theorem sub7462 (p : Pattern) : d1844 (change p 204 none) = d5015 p := by
  change (if p 160 then d1766 (change p 204 none) else d1843 (change p 204 none)) = d5015 p
  rw [sub7381, sub7461]
  rfl
theorem sub7463 (p : Pattern) : d1845 (change p 204 none) = d5016 p := by
  change (if p 141 then d1844 (change p 204 none) else d1840 (change p 204 none)) = d5016 p
  rw [sub7462, sub7458]
  rfl
theorem sub7464 (p : Pattern) : d1846 (change p 204 none) = d5045 p := by
  change (if p 138 then d1825 (change p 204 none) else d1845 (change p 204 none)) = d5045 p
  rw [sub7443, sub7463]
  rfl
theorem sub7465 (p : Pattern) : d1847 (change p 204 none) = d5056 p := by
  change (if p 138 then d12 (change p 204 none) else d1825 (change p 204 none)) = d5056 p
  rw [sub7260, sub7443]
  rfl
theorem sub7466 (p : Pattern) : d1848 (change p 204 none) = d5057 p := by
  change (if p 116 then d1847 (change p 204 none) else d1846 (change p 204 none)) = d5057 p
  rw [sub7465, sub7464]
  rfl
theorem sub7467 (p : Pattern) : d1849 (change p 204 none) = d5058 p := by
  change (if p 115 then d1848 (change p 204 none) else d1836 (change p 204 none)) = d5058 p
  rw [sub7466, sub7454]
  rfl
theorem sub7468 (p : Pattern) : d1850 (change p 204 none) = d14 p := by
  change d14 (change p 204 none) = d14 p
  exact sub7262 p
theorem sub7469 (p : Pattern) : d1851 (change p 204 none) = d4986 p := by
  change (if p 182 then d1687 (change p 204 none) else d1850 (change p 204 none)) = d4986 p
  rw [sub7270, sub7468]
  rfl
theorem sub7470 (p : Pattern) : d1852 (change p 204 none) = d4986 p := by
  change (if p 163 then d1692 (change p 204 none) else d1851 (change p 204 none)) = d4986 p
  rw [sub7276, sub7469]
  simp only [ite_self]
theorem sub7471 (p : Pattern) : d1853 (change p 204 none) = d4989 p := by
  change (if p 162 then d1699 (change p 204 none) else d1852 (change p 204 none)) = d4989 p
  rw [sub7289, sub7470]
  rfl
theorem sub7472 (p : Pattern) : d1854 (change p 204 none) = d4993 p := by
  change (if p 161 then d1708 (change p 204 none) else d1853 (change p 204 none)) = d4993 p
  rw [sub7304, sub7471]
  rfl
theorem sub7473 (p : Pattern) : d1855 (change p 204 none) = d5001 p := by
  change (if p 160 then d1738 (change p 204 none) else d1854 (change p 204 none)) = d5001 p
  rw [sub7345, sub7472]
  rfl
theorem sub7474 (p : Pattern) : d1856 (change p 204 none) = d5003 p := by
  change (if p 163 then d1747 (change p 204 none) else d1690 (change p 204 none)) = d5003 p
  rw [sub7355, sub7273]
  rfl
theorem sub7475 (p : Pattern) : d1857 (change p 204 none) = d5005 p := by
  change (if p 162 then d1749 (change p 204 none) else d1856 (change p 204 none)) = d5005 p
  rw [sub7357, sub7474]
  rfl
theorem sub7476 (p : Pattern) : d1858 (change p 204 none) = d5011 p := by
  change (if p 161 then d1758 (change p 204 none) else d1857 (change p 204 none)) = d5011 p
  rw [sub7370, sub7475]
  rfl
theorem sub7477 (p : Pattern) : d1859 (change p 204 none) = d5015 p := by
  change (if p 160 then d1766 (change p 204 none) else d1858 (change p 204 none)) = d5015 p
  rw [sub7381, sub7476]
  rfl
theorem sub7478 (p : Pattern) : d1860 (change p 204 none) = d5016 p := by
  change (if p 141 then d1859 (change p 204 none) else d1855 (change p 204 none)) = d5016 p
  rw [sub7477, sub7473]
  rfl
theorem sub7479 (p : Pattern) : d1861 (change p 204 none) = d5045 p := by
  change (if p 138 then d1825 (change p 204 none) else d1860 (change p 204 none)) = d5045 p
  rw [sub7443, sub7478]
  rfl
theorem sub7480 (p : Pattern) : d1862 (change p 204 none) = d5055 p := by
  change (if p 116 then d1835 (change p 204 none) else d1861 (change p 204 none)) = d5055 p
  rw [sub7453, sub7479]
  rfl
theorem sub7481 (p : Pattern) : d1863 (change p 204 none) = d4989 p := by
  change (if p 162 then d1699 (change p 204 none) else d1692 (change p 204 none)) = d4989 p
  rw [sub7289, sub7276]
  rfl
theorem sub7482 (p : Pattern) : d1864 (change p 204 none) = d4993 p := by
  change (if p 161 then d1708 (change p 204 none) else d1863 (change p 204 none)) = d4993 p
  rw [sub7304, sub7481]
  rfl
theorem sub7483 (p : Pattern) : d1865 (change p 204 none) = d5001 p := by
  change (if p 160 then d1738 (change p 204 none) else d1864 (change p 204 none)) = d5001 p
  rw [sub7345, sub7482]
  rfl
theorem sub7484 (p : Pattern) : d1866 (change p 204 none) = d5016 p := by
  change (if p 141 then d1844 (change p 204 none) else d1865 (change p 204 none)) = d5016 p
  rw [sub7462, sub7483]
  rfl
theorem sub7485 (p : Pattern) : d1867 (change p 204 none) = d5045 p := by
  change (if p 138 then d1825 (change p 204 none) else d1866 (change p 204 none)) = d5045 p
  rw [sub7443, sub7484]
  rfl
theorem sub7486 (p : Pattern) : d1868 (change p 204 none) = d5057 p := by
  change (if p 116 then d1847 (change p 204 none) else d1867 (change p 204 none)) = d5057 p
  rw [sub7465, sub7485]
  rfl
theorem sub7487 (p : Pattern) : d1869 (change p 204 none) = d5058 p := by
  change (if p 115 then d1868 (change p 204 none) else d1862 (change p 204 none)) = d5058 p
  rw [sub7486, sub7480]
  rfl
theorem sub7488 (p : Pattern) : d1870 (change p 204 none) = d5058 p := by
  change (if p 71 then d1869 (change p 204 none) else d1849 (change p 204 none)) = d5058 p
  rw [sub7487, sub7467]
  simp only [ite_self]
theorem sub7489 (p : Pattern) : d1 (change p 204 none) = d1 p := by
  rfl
theorem sub7490 (p : Pattern) : d102 (change p 204 none) = d102 p := by
  change (if p 247 then d12 (change p 204 none) else d1 (change p 204 none)) = d102 p
  rw [sub7260, sub7489]
  rfl
theorem sub7491 (p : Pattern) : d103 (change p 204 none) = d103 p := by
  change (if p 246 then d102 (change p 204 none) else d1 (change p 204 none)) = d103 p
  rw [sub7490, sub7489]
  rfl
theorem sub7492 (p : Pattern) : d1871 (change p 204 none) = d103 p := by
  change d103 (change p 204 none) = d103 p
  exact sub7491 p
theorem sub7493 (p : Pattern) : d3 (change p 204 none) = d3 p := by
  rfl
theorem sub7494 (p : Pattern) : d1872 (change p 204 none) = d1872 p := by
  change (if p 247 then d3 (change p 204 none) else d1 (change p 204 none)) = d1872 p
  rw [sub7493, sub7489]
  rfl
theorem sub7495 (p : Pattern) : d115 (change p 204 none) = d115 p := by
  change (if p 247 then d12 (change p 204 none) else d3 (change p 204 none)) = d115 p
  rw [sub7260, sub7493]
  rfl
theorem sub7496 (p : Pattern) : d1873 (change p 204 none) = d1873 p := by
  change (if p 246 then d115 (change p 204 none) else d1872 (change p 204 none)) = d1873 p
  rw [sub7495, sub7494]
  rfl
theorem sub7497 (p : Pattern) : d1874 (change p 204 none) = d1874 p := by
  change (if p 225 then d1873 (change p 204 none) else d103 (change p 204 none)) = d1874 p
  rw [sub7496, sub7491]
  rfl
theorem sub7498 (p : Pattern) : d1875 (change p 204 none) = d1875 p := by
  change (if p 224 then d1873 (change p 204 none) else d1874 (change p 204 none)) = d1875 p
  rw [sub7496, sub7497]
  rfl
theorem sub7499 (p : Pattern) : d1876 (change p 204 none) = d1875 p := by
  change d1875 (change p 204 none) = d1875 p
  exact sub7498 p
theorem sub7500 (p : Pattern) : d1877 (change p 204 none) = d5059 p := by
  change (if p 182 then d1876 (change p 204 none) else d1871 (change p 204 none)) = d5059 p
  rw [sub7499, sub7492]
  rfl
theorem sub7501 (p : Pattern) : d104 (change p 204 none) = d103 p := by
  change d103 (change p 204 none) = d103 p
  exact sub7491 p
theorem sub7502 (p : Pattern) : d1878 (change p 204 none) = d5059 p := by
  change (if p 182 then d1876 (change p 204 none) else d104 (change p 204 none)) = d5059 p
  rw [sub7499, sub7501]
  rfl
theorem sub7503 (p : Pattern) : d1879 (change p 204 none) = d5059 p := by
  change (if p 163 then d1878 (change p 204 none) else d1877 (change p 204 none)) = d5059 p
  rw [sub7502, sub7500]
  simp only [ite_self]
theorem sub7504 (p : Pattern) : d5 (change p 204 none) = d5 p := by
  rfl
theorem sub7505 (p : Pattern) : d106 (change p 204 none) = d106 p := by
  change (if p 247 then d12 (change p 204 none) else d5 (change p 204 none)) = d106 p
  rw [sub7260, sub7504]
  rfl
theorem sub7506 (p : Pattern) : d107 (change p 204 none) = d107 p := by
  change (if p 246 then d106 (change p 204 none) else d5 (change p 204 none)) = d107 p
  rw [sub7505, sub7504]
  rfl
theorem sub7507 (p : Pattern) : d108 (change p 204 none) = d107 p := by
  change d107 (change p 204 none) = d107 p
  exact sub7506 p
theorem sub7508 (p : Pattern) : d7 (change p 204 none) = d7 p := by
  rfl
theorem sub7509 (p : Pattern) : d1880 (change p 204 none) = d1880 p := by
  change (if p 247 then d7 (change p 204 none) else d5 (change p 204 none)) = d1880 p
  rw [sub7508, sub7504]
  rfl
theorem sub7510 (p : Pattern) : d119 (change p 204 none) = d119 p := by
  change (if p 247 then d12 (change p 204 none) else d7 (change p 204 none)) = d119 p
  rw [sub7260, sub7508]
  rfl
theorem sub7511 (p : Pattern) : d1881 (change p 204 none) = d1881 p := by
  change (if p 246 then d119 (change p 204 none) else d1880 (change p 204 none)) = d1881 p
  rw [sub7510, sub7509]
  rfl
theorem sub7512 (p : Pattern) : d1882 (change p 204 none) = d1882 p := by
  change (if p 225 then d1881 (change p 204 none) else d107 (change p 204 none)) = d1882 p
  rw [sub7511, sub7506]
  rfl
theorem sub7513 (p : Pattern) : d1883 (change p 204 none) = d1883 p := by
  change (if p 224 then d1881 (change p 204 none) else d1882 (change p 204 none)) = d1883 p
  rw [sub7511, sub7512]
  rfl
theorem sub7514 (p : Pattern) : d1884 (change p 204 none) = d1883 p := by
  change d1883 (change p 204 none) = d1883 p
  exact sub7513 p
theorem sub7515 (p : Pattern) : d1885 (change p 204 none) = d5060 p := by
  change (if p 182 then d1884 (change p 204 none) else d108 (change p 204 none)) = d5060 p
  rw [sub7514, sub7507]
  rfl
theorem sub7516 (p : Pattern) : d1886 (change p 204 none) = d5061 p := by
  change (if p 163 then d1885 (change p 204 none) else d1878 (change p 204 none)) = d5061 p
  rw [sub7515, sub7502]
  rfl
theorem sub7517 (p : Pattern) : d1887 (change p 204 none) = d5062 p := by
  change (if p 162 then d1886 (change p 204 none) else d1879 (change p 204 none)) = d5062 p
  rw [sub7516, sub7503]
  rfl
theorem sub7518 (p : Pattern) : d1888 (change p 204 none) = d5063 p := by
  change (if p 163 then d12 (change p 204 none) else d1754 (change p 204 none)) = d5063 p
  rw [sub7260, sub7365]
  rfl
theorem sub7519 (p : Pattern) : d1889 (change p 204 none) = d5064 p := by
  change (if p 162 then d1888 (change p 204 none) else d1886 (change p 204 none)) = d5064 p
  rw [sub7518, sub7516]
  rfl
theorem sub7520 (p : Pattern) : d1890 (change p 204 none) = d5065 p := by
  change (if p 161 then d1889 (change p 204 none) else d1887 (change p 204 none)) = d5065 p
  rw [sub7519, sub7517]
  rfl
theorem sub7521 (p : Pattern) : d116 (change p 204 none) = d116 p := by
  change (if p 246 then d115 (change p 204 none) else d3 (change p 204 none)) = d116 p
  rw [sub7495, sub7493]
  rfl
theorem sub7522 (p : Pattern) : d1891 (change p 204 none) = d1891 p := by
  change (if p 247 then d9 (change p 204 none) else d3 (change p 204 none)) = d1891 p
  rw [sub7291, sub7493]
  rfl
theorem sub7523 (p : Pattern) : d1892 (change p 204 none) = d1892 p := by
  change (if p 246 then d23 (change p 204 none) else d1891 (change p 204 none)) = d1892 p
  rw [sub7292, sub7522]
  rfl
theorem sub7524 (p : Pattern) : d1893 (change p 204 none) = d1893 p := by
  change (if p 225 then d1892 (change p 204 none) else d116 (change p 204 none)) = d1893 p
  rw [sub7523, sub7521]
  rfl
theorem sub7525 (p : Pattern) : d1894 (change p 204 none) = d1894 p := by
  change (if p 247 then d7 (change p 204 none) else d3 (change p 204 none)) = d1894 p
  rw [sub7508, sub7493]
  rfl
theorem sub7526 (p : Pattern) : d1895 (change p 204 none) = d1895 p := by
  change (if p 246 then d119 (change p 204 none) else d1894 (change p 204 none)) = d1895 p
  rw [sub7510, sub7525]
  rfl
theorem sub7527 (p : Pattern) : d1896 (change p 204 none) = d1896 p := by
  change (if p 246 then d12 (change p 204 none) else d115 (change p 204 none)) = d1896 p
  rw [sub7260, sub7495]
  rfl
theorem sub7528 (p : Pattern) : d1897 (change p 204 none) = d1897 p := by
  change (if p 225 then d1896 (change p 204 none) else d1895 (change p 204 none)) = d1897 p
  rw [sub7527, sub7526]
  rfl
theorem sub7529 (p : Pattern) : d1898 (change p 204 none) = d1898 p := by
  change (if p 224 then d1897 (change p 204 none) else d1893 (change p 204 none)) = d1898 p
  rw [sub7528, sub7524]
  rfl
theorem sub7530 (p : Pattern) : d1899 (change p 204 none) = d1898 p := by
  change d1898 (change p 204 none) = d1898 p
  exact sub7529 p
theorem sub7531 (p : Pattern) : d1900 (change p 204 none) = d5066 p := by
  change (if p 182 then d1899 (change p 204 none) else d104 (change p 204 none)) = d5066 p
  rw [sub7530, sub7501]
  rfl
theorem sub7532 (p : Pattern) : d120 (change p 204 none) = d120 p := by
  change (if p 246 then d119 (change p 204 none) else d7 (change p 204 none)) = d120 p
  rw [sub7510, sub7508]
  rfl
theorem sub7533 (p : Pattern) : d317 (change p 204 none) = d317 p := by
  change (if p 246 then d12 (change p 204 none) else d119 (change p 204 none)) = d317 p
  rw [sub7260, sub7510]
  rfl
theorem sub7534 (p : Pattern) : d1901 (change p 204 none) = d1901 p := by
  change (if p 225 then d317 (change p 204 none) else d120 (change p 204 none)) = d1901 p
  rw [sub7533, sub7532]
  rfl
theorem sub7535 (p : Pattern) : d1902 (change p 204 none) = d1902 p := by
  change (if p 247 then d11 (change p 204 none) else d7 (change p 204 none)) = d1902 p
  rw [sub7295, sub7508]
  rfl
theorem sub7536 (p : Pattern) : d1903 (change p 204 none) = d1903 p := by
  change (if p 246 then d39 (change p 204 none) else d1902 (change p 204 none)) = d1903 p
  rw [sub7297, sub7535]
  rfl
theorem sub7537 (p : Pattern) : d1904 (change p 204 none) = d1904 p := by
  change (if p 225 then d317 (change p 204 none) else d1903 (change p 204 none)) = d1904 p
  rw [sub7533, sub7536]
  rfl
theorem sub7538 (p : Pattern) : d1905 (change p 204 none) = d1905 p := by
  change (if p 224 then d1904 (change p 204 none) else d1901 (change p 204 none)) = d1905 p
  rw [sub7537, sub7534]
  rfl
theorem sub7539 (p : Pattern) : d1906 (change p 204 none) = d1905 p := by
  change d1905 (change p 204 none) = d1905 p
  exact sub7538 p
theorem sub7540 (p : Pattern) : d1907 (change p 204 none) = d5067 p := by
  change (if p 182 then d1906 (change p 204 none) else d104 (change p 204 none)) = d5067 p
  rw [sub7539, sub7501]
  rfl
theorem sub7541 (p : Pattern) : d1908 (change p 204 none) = d5068 p := by
  change (if p 163 then d1907 (change p 204 none) else d1900 (change p 204 none)) = d5068 p
  rw [sub7540, sub7531]
  rfl
theorem sub7542 (p : Pattern) : d1909 (change p 204 none) = d124 p := by
  change (if p 182 then d12 (change p 204 none) else d104 (change p 204 none)) = d124 p
  rw [sub7260, sub7501]
  rfl
theorem sub7543 (p : Pattern) : d1910 (change p 204 none) = d125 p := by
  change (if p 182 then d12 (change p 204 none) else d108 (change p 204 none)) = d125 p
  rw [sub7260, sub7507]
  rfl
theorem sub7544 (p : Pattern) : d1911 (change p 204 none) = d126 p := by
  change (if p 163 then d1910 (change p 204 none) else d1909 (change p 204 none)) = d126 p
  rw [sub7543, sub7542]
  rfl
theorem sub7545 (p : Pattern) : d1912 (change p 204 none) = d5069 p := by
  change (if p 162 then d1911 (change p 204 none) else d1908 (change p 204 none)) = d5069 p
  rw [sub7544, sub7541]
  rfl
theorem sub7546 (p : Pattern) : d278 (change p 204 none) = d128 p := by
  change (if p 163 then d12 (change p 204 none) else d277 (change p 204 none)) = d128 p
  rw [sub7260, sub7376]
  rfl
theorem sub7547 (p : Pattern) : d1913 (change p 204 none) = d129 p := by
  change (if p 162 then d278 (change p 204 none) else d1911 (change p 204 none)) = d129 p
  rw [sub7546, sub7544]
  rfl
theorem sub7548 (p : Pattern) : d1914 (change p 204 none) = d5070 p := by
  change (if p 161 then d1913 (change p 204 none) else d1912 (change p 204 none)) = d5070 p
  rw [sub7547, sub7545]
  rfl
theorem sub7549 (p : Pattern) : d1915 (change p 204 none) = d5071 p := by
  change (if p 160 then d1914 (change p 204 none) else d1890 (change p 204 none)) = d5071 p
  rw [sub7548, sub7520]
  rfl
theorem sub7550 (p : Pattern) : d1916 (change p 204 none) = d103 p := by
  change d103 (change p 204 none) = d103 p
  exact sub7491 p
theorem sub7551 (p : Pattern) : d1917 (change p 204 none) = d5059 p := by
  change (if p 182 then d1876 (change p 204 none) else d1916 (change p 204 none)) = d5059 p
  rw [sub7499, sub7550]
  rfl
theorem sub7552 (p : Pattern) : d117 (change p 204 none) = d116 p := by
  change d116 (change p 204 none) = d116 p
  exact sub7521 p
theorem sub7553 (p : Pattern) : d1918 (change p 204 none) = d1918 p := by
  change (if p 247 then d5 (change p 204 none) else d3 (change p 204 none)) = d1918 p
  rw [sub7504, sub7493]
  rfl
theorem sub7554 (p : Pattern) : d1919 (change p 204 none) = d1919 p := by
  change (if p 246 then d106 (change p 204 none) else d1918 (change p 204 none)) = d1919 p
  rw [sub7505, sub7553]
  rfl
theorem sub7555 (p : Pattern) : d1920 (change p 204 none) = d1920 p := by
  change (if p 225 then d1919 (change p 204 none) else d116 (change p 204 none)) = d1920 p
  rw [sub7554, sub7521]
  rfl
theorem sub7556 (p : Pattern) : d1921 (change p 204 none) = d1921 p := by
  change (if p 224 then d1919 (change p 204 none) else d1920 (change p 204 none)) = d1921 p
  rw [sub7554, sub7555]
  rfl
theorem sub7557 (p : Pattern) : d1922 (change p 204 none) = d1921 p := by
  change d1921 (change p 204 none) = d1921 p
  exact sub7556 p
theorem sub7558 (p : Pattern) : d1923 (change p 204 none) = d5072 p := by
  change (if p 182 then d1922 (change p 204 none) else d117 (change p 204 none)) = d5072 p
  rw [sub7557, sub7552]
  rfl
theorem sub7559 (p : Pattern) : d1924 (change p 204 none) = d5073 p := by
  change (if p 163 then d1923 (change p 204 none) else d1917 (change p 204 none)) = d5073 p
  rw [sub7558, sub7551]
  rfl
end NetHack.Sokoban22Refined85
