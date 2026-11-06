/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions63
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub7680 (p : Pattern) : d2043 (change p 204 none) = d184 p := by
  change (if p 162 then d12 (change p 204 none) else d2042 (change p 204 none)) = d184 p
  rw [sub7260, sub7679]
  rfl
theorem sub7681 (p : Pattern) : d2044 (change p 204 none) = d5143 p := by
  change (if p 161 then d2043 (change p 204 none) else d2041 (change p 204 none)) = d5143 p
  rw [sub7680, sub7678]
  rfl
theorem sub7682 (p : Pattern) : d2045 (change p 204 none) = d5144 p := by
  change (if p 160 then d2044 (change p 204 none) else d2038 (change p 204 none)) = d5144 p
  rw [sub7681, sub7675]
  rfl
theorem sub7683 (p : Pattern) : d2046 (change p 204 none) = d5145 p := by
  change (if p 141 then d2045 (change p 204 none) else d2028 (change p 204 none)) = d5145 p
  rw [sub7682, sub7665]
  rfl
theorem sub7684 (p : Pattern) : d2047 (change p 204 none) = d2047 p := by
  change (if p 225 then d1776 (change p 204 none) else d1770 (change p 204 none)) = d2047 p
  rw [sub7391, sub7385]
  rfl
theorem sub7685 (p : Pattern) : d2048 (change p 204 none) = d2048 p := by
  change (if p 224 then d2047 (change p 204 none) else d1777 (change p 204 none)) = d2048 p
  rw [sub7684, sub7392]
  rfl
theorem sub7686 (p : Pattern) : d2049 (change p 204 none) = d2048 p := by
  change d2048 (change p 204 none) = d2048 p
  exact sub7685 p
theorem sub7687 (p : Pattern) : d2050 (change p 204 none) = d5146 p := by
  change (if p 182 then d2049 (change p 204 none) else d15 (change p 204 none)) = d5146 p
  rw [sub7686, sub7275]
  rfl
theorem sub7688 (p : Pattern) : d2051 (change p 204 none) = d2051 p := by
  change (if p 247 then d10 (change p 204 none) else d0 (change p 204 none)) = d2051 p
  rw [sub7322, sub7259]
  rfl
theorem sub7689 (p : Pattern) : d2052 (change p 204 none) = d2052 p := by
  change (if p 246 then d23 (change p 204 none) else d2051 (change p 204 none)) = d2052 p
  rw [sub7292, sub7688]
  rfl
theorem sub7690 (p : Pattern) : d2053 (change p 204 none) = d2053 p := by
  change (if p 225 then d2052 (change p 204 none) else d1770 (change p 204 none)) = d2053 p
  rw [sub7689, sub7385]
  rfl
theorem sub7691 (p : Pattern) : d2054 (change p 204 none) = d2054 p := by
  change (if p 224 then d2053 (change p 204 none) else d1777 (change p 204 none)) = d2054 p
  rw [sub7690, sub7392]
  rfl
theorem sub7692 (p : Pattern) : d2055 (change p 204 none) = d2054 p := by
  change d2054 (change p 204 none) = d2054 p
  exact sub7691 p
theorem sub7693 (p : Pattern) : d2056 (change p 204 none) = d5147 p := by
  change (if p 182 then d2055 (change p 204 none) else d15 (change p 204 none)) = d5147 p
  rw [sub7692, sub7275]
  rfl
theorem sub7694 (p : Pattern) : d2057 (change p 204 none) = d5148 p := by
  change (if p 163 then d2056 (change p 204 none) else d2050 (change p 204 none)) = d5148 p
  rw [sub7693, sub7687]
  rfl
theorem sub7695 (p : Pattern) : d2058 (change p 204 none) = d5149 p := by
  change (if p 162 then d1811 (change p 204 none) else d2057 (change p 204 none)) = d5149 p
  rw [sub7429, sub7694]
  rfl
theorem sub7696 (p : Pattern) : d2059 (change p 204 none) = d5150 p := by
  change (if p 161 then d1812 (change p 204 none) else d2058 (change p 204 none)) = d5150 p
  rw [sub7430, sub7695]
  rfl
theorem sub7697 (p : Pattern) : d191 (change p 204 none) = d191 p := by
  change (if p 246 then d190 (change p 204 none) else d8 (change p 204 none)) = d191 p
  rw [sub7309, sub7307]
  rfl
theorem sub7698 (p : Pattern) : d192 (change p 204 none) = d191 p := by
  change d191 (change p 204 none) = d191 p
  exact sub7697 p
theorem sub7699 (p : Pattern) : d315 (change p 204 none) = d315 p := by
  change (if p 246 then d12 (change p 204 none) else d190 (change p 204 none)) = d315 p
  rw [sub7260, sub7309]
  rfl
theorem sub7700 (p : Pattern) : d2060 (change p 204 none) = d2060 p := by
  change (if p 225 then d315 (change p 204 none) else d191 (change p 204 none)) = d2060 p
  rw [sub7699, sub7697]
  rfl
theorem sub7701 (p : Pattern) : d2061 (change p 204 none) = d2061 p := by
  change (if p 224 then d315 (change p 204 none) else d2060 (change p 204 none)) = d2061 p
  rw [sub7699, sub7700]
  rfl
theorem sub7702 (p : Pattern) : d2062 (change p 204 none) = d2061 p := by
  change d2061 (change p 204 none) = d2061 p
  exact sub7701 p
theorem sub7703 (p : Pattern) : d2063 (change p 204 none) = d5151 p := by
  change (if p 182 then d2062 (change p 204 none) else d192 (change p 204 none)) = d5151 p
  rw [sub7702, sub7698]
  rfl
theorem sub7704 (p : Pattern) : d2064 (change p 204 none) = d5152 p := by
  change (if p 163 then d2063 (change p 204 none) else d1799 (change p 204 none)) = d5152 p
  rw [sub7703, sub7415]
  rfl
theorem sub7705 (p : Pattern) : d2065 (change p 204 none) = d5153 p := by
  change (if p 162 then d12 (change p 204 none) else d2064 (change p 204 none)) = d5153 p
  rw [sub7260, sub7704]
  rfl
theorem sub7706 (p : Pattern) : d2066 (change p 204 none) = d5154 p := by
  change (if p 161 then d12 (change p 204 none) else d2065 (change p 204 none)) = d5154 p
  rw [sub7260, sub7705]
  rfl
theorem sub7707 (p : Pattern) : d2067 (change p 204 none) = d5155 p := by
  change (if p 160 then d2066 (change p 204 none) else d2059 (change p 204 none)) = d5155 p
  rw [sub7706, sub7696]
  rfl
theorem sub7708 (p : Pattern) : d2068 (change p 204 none) = d2068 p := by
  change (if p 247 then d10 (change p 204 none) else d2 (change p 204 none)) = d2068 p
  rw [sub7322, sub7264]
  rfl
theorem sub7709 (p : Pattern) : d2069 (change p 204 none) = d2069 p := by
  change (if p 246 then d57 (change p 204 none) else d2068 (change p 204 none)) = d2069 p
  rw [sub7324, sub7708]
  rfl
theorem sub7710 (p : Pattern) : d2070 (change p 204 none) = d2070 p := by
  change (if p 225 then d2069 (change p 204 none) else d1714 (change p 204 none)) = d2070 p
  rw [sub7709, sub7313]
  rfl
theorem sub7711 (p : Pattern) : d2071 (change p 204 none) = d2071 p := by
  change (if p 224 then d2070 (change p 204 none) else d1712 (change p 204 none)) = d2071 p
  rw [sub7710, sub7311]
  rfl
theorem sub7712 (p : Pattern) : d2072 (change p 204 none) = d2071 p := by
  change d2071 (change p 204 none) = d2071 p
  exact sub7711 p
theorem sub7713 (p : Pattern) : d2073 (change p 204 none) = d5156 p := by
  change (if p 182 then d2072 (change p 204 none) else d32 (change p 204 none)) = d5156 p
  rw [sub7712, sub7349]
  rfl
theorem sub7714 (p : Pattern) : d2074 (change p 204 none) = d5157 p := by
  change (if p 163 then d1809 (change p 204 none) else d2073 (change p 204 none)) = d5157 p
  rw [sub7426, sub7713]
  rfl
theorem sub7715 (p : Pattern) : d2075 (change p 204 none) = d5158 p := by
  change (if p 163 then d1756 (change p 204 none) else d1799 (change p 204 none)) = d5158 p
  rw [sub7368, sub7415]
  rfl
theorem sub7716 (p : Pattern) : d2076 (change p 204 none) = d5159 p := by
  change (if p 162 then d2075 (change p 204 none) else d2074 (change p 204 none)) = d5159 p
  rw [sub7715, sub7714]
  rfl
theorem sub7717 (p : Pattern) : d2077 (change p 204 none) = d5160 p := by
  change (if p 161 then d1822 (change p 204 none) else d2076 (change p 204 none)) = d5160 p
  rw [sub7440, sub7716]
  rfl
theorem sub7718 (p : Pattern) : d2078 (change p 204 none) = d5161 p := by
  change (if p 163 then d12 (change p 204 none) else d2063 (change p 204 none)) = d5161 p
  rw [sub7260, sub7703]
  rfl
theorem sub7719 (p : Pattern) : d2079 (change p 204 none) = d5162 p := by
  change (if p 162 then d12 (change p 204 none) else d2078 (change p 204 none)) = d5162 p
  rw [sub7260, sub7718]
  rfl
theorem sub7720 (p : Pattern) : d2080 (change p 204 none) = d5163 p := by
  change (if p 161 then d12 (change p 204 none) else d2079 (change p 204 none)) = d5163 p
  rw [sub7260, sub7719]
  rfl
theorem sub7721 (p : Pattern) : d2081 (change p 204 none) = d5164 p := by
  change (if p 160 then d2080 (change p 204 none) else d2077 (change p 204 none)) = d5164 p
  rw [sub7720, sub7717]
  rfl
theorem sub7722 (p : Pattern) : d2082 (change p 204 none) = d5165 p := by
  change (if p 141 then d2081 (change p 204 none) else d2067 (change p 204 none)) = d5165 p
  rw [sub7721, sub7707]
  rfl
theorem sub7723 (p : Pattern) : d2083 (change p 204 none) = d5166 p := by
  change (if p 138 then d2082 (change p 204 none) else d2046 (change p 204 none)) = d5166 p
  rw [sub7722, sub7683]
  rfl
theorem sub7724 (p : Pattern) : d2084 (change p 204 none) = d5167 p := by
  change (if p 138 then d12 (change p 204 none) else d2082 (change p 204 none)) = d5167 p
  rw [sub7260, sub7722]
  rfl
theorem sub7725 (p : Pattern) : d2085 (change p 204 none) = d5168 p := by
  change (if p 116 then d2084 (change p 204 none) else d2083 (change p 204 none)) = d5168 p
  rw [sub7724, sub7723]
  rfl
theorem sub7726 (p : Pattern) : d2086 (change p 204 none) = d5169 p := by
  change (if p 115 then d2085 (change p 204 none) else d1862 (change p 204 none)) = d5169 p
  rw [sub7725, sub7480]
  rfl
theorem sub7727 (p : Pattern) : d2087 (change p 204 none) = d5170 p := by
  change (if p 71 then d2086 (change p 204 none) else d1849 (change p 204 none)) = d5170 p
  rw [sub7726, sub7467]
  rfl
theorem sub7728 (p : Pattern) : d2088 (change p 204 none) = d5171 p := by
  change (if p 163 then d12 (change p 204 none) else d1885 (change p 204 none)) = d5171 p
  rw [sub7260, sub7515]
  rfl
theorem sub7729 (p : Pattern) : d2089 (change p 204 none) = d5172 p := by
  change (if p 162 then d2088 (change p 204 none) else d1924 (change p 204 none)) = d5172 p
  rw [sub7728, sub7559]
  rfl
theorem sub7730 (p : Pattern) : d2090 (change p 204 none) = d5173 p := by
  change (if p 162 then d12 (change p 204 none) else d2088 (change p 204 none)) = d5173 p
  rw [sub7260, sub7728]
  rfl
theorem sub7731 (p : Pattern) : d2091 (change p 204 none) = d5174 p := by
  change (if p 161 then d2090 (change p 204 none) else d2089 (change p 204 none)) = d5174 p
  rw [sub7730, sub7729]
  rfl
theorem sub7732 (p : Pattern) : d2092 (change p 204 none) = d215 p := by
  change (if p 163 then d12 (change p 204 none) else d1910 (change p 204 none)) = d215 p
  rw [sub7260, sub7543]
  rfl
theorem sub7733 (p : Pattern) : d2093 (change p 204 none) = d5175 p := by
  change (if p 162 then d2092 (change p 204 none) else d1931 (change p 204 none)) = d5175 p
  rw [sub7732, sub7566]
  rfl
theorem sub7734 (p : Pattern) : d2094 (change p 204 none) = d217 p := by
  change (if p 162 then d12 (change p 204 none) else d2092 (change p 204 none)) = d217 p
  rw [sub7260, sub7732]
  rfl
theorem sub7735 (p : Pattern) : d2095 (change p 204 none) = d5176 p := by
  change (if p 161 then d2094 (change p 204 none) else d2093 (change p 204 none)) = d5176 p
  rw [sub7734, sub7733]
  rfl
theorem sub7736 (p : Pattern) : d2096 (change p 204 none) = d5177 p := by
  change (if p 160 then d2095 (change p 204 none) else d2091 (change p 204 none)) = d5177 p
  rw [sub7735, sub7731]
  rfl
theorem sub7737 (p : Pattern) : d2097 (change p 204 none) = d5178 p := by
  change (if p 141 then d2096 (change p 204 none) else d1915 (change p 204 none)) = d5178 p
  rw [sub7736, sub7549]
  rfl
theorem sub7738 (p : Pattern) : d2098 (change p 204 none) = d5179 p := by
  change (if p 163 then d12 (change p 204 none) else d1968 (change p 204 none)) = d5179 p
  rw [sub7260, sub7604]
  rfl
theorem sub7739 (p : Pattern) : d2099 (change p 204 none) = d5180 p := by
  change (if p 162 then d2098 (change p 204 none) else d1979 (change p 204 none)) = d5180 p
  rw [sub7738, sub7616]
  rfl
theorem sub7740 (p : Pattern) : d2100 (change p 204 none) = d5181 p := by
  change (if p 162 then d12 (change p 204 none) else d2098 (change p 204 none)) = d5181 p
  rw [sub7260, sub7738]
  rfl
theorem sub7741 (p : Pattern) : d2101 (change p 204 none) = d5182 p := by
  change (if p 161 then d2100 (change p 204 none) else d2099 (change p 204 none)) = d5182 p
  rw [sub7740, sub7739]
  rfl
theorem sub7742 (p : Pattern) : d2102 (change p 204 none) = d5183 p := by
  change (if p 160 then d1987 (change p 204 none) else d2101 (change p 204 none)) = d5183 p
  rw [sub7624, sub7741]
  rfl
theorem sub7743 (p : Pattern) : d2103 (change p 204 none) = d5184 p := by
  change (if p 141 then d2102 (change p 204 none) else d1978 (change p 204 none)) = d5184 p
  rw [sub7742, sub7615]
  rfl
theorem sub7744 (p : Pattern) : d2104 (change p 204 none) = d5185 p := by
  change (if p 138 then d2103 (change p 204 none) else d2097 (change p 204 none)) = d5185 p
  rw [sub7743, sub7737]
  rfl
theorem sub7745 (p : Pattern) : d2105 (change p 204 none) = d5186 p := by
  change (if p 138 then d1994 (change p 204 none) else d2103 (change p 204 none)) = d5186 p
  rw [sub7631, sub7743]
  rfl
theorem sub7746 (p : Pattern) : d2106 (change p 204 none) = d5187 p := by
  change (if p 116 then d2105 (change p 204 none) else d2104 (change p 204 none)) = d5187 p
  rw [sub7745, sub7744]
  rfl
theorem sub7747 (p : Pattern) : d2107 (change p 204 none) = d2107 p := by
  change (if p 225 then d1946 (change p 204 none) else d1940 (change p 204 none)) = d2107 p
  rw [sub7581, sub7575]
  rfl
theorem sub7748 (p : Pattern) : d2108 (change p 204 none) = d2108 p := by
  change (if p 224 then d2107 (change p 204 none) else d1947 (change p 204 none)) = d2108 p
  rw [sub7747, sub7582]
  rfl
theorem sub7749 (p : Pattern) : d2109 (change p 204 none) = d2108 p := by
  change d2108 (change p 204 none) = d2108 p
  exact sub7748 p
theorem sub7750 (p : Pattern) : d2110 (change p 204 none) = d5188 p := by
  change (if p 182 then d2109 (change p 204 none) else d104 (change p 204 none)) = d5188 p
  rw [sub7749, sub7501]
  rfl
theorem sub7751 (p : Pattern) : d2111 (change p 204 none) = d5189 p := by
  change (if p 163 then d1968 (change p 204 none) else d2110 (change p 204 none)) = d5189 p
  rw [sub7604, sub7750]
  rfl
theorem sub7752 (p : Pattern) : d2112 (change p 204 none) = d5190 p := by
  change (if p 162 then d2111 (change p 204 none) else d1944 (change p 204 none)) = d5190 p
  rw [sub7751, sub7579]
  rfl
theorem sub7753 (p : Pattern) : d2113 (change p 204 none) = d5191 p := by
  change (if p 163 then d1968 (change p 204 none) else d1953 (change p 204 none)) = d5191 p
  rw [sub7604, sub7588]
  rfl
theorem sub7754 (p : Pattern) : d2114 (change p 204 none) = d5192 p := by
  change (if p 162 then d1888 (change p 204 none) else d2113 (change p 204 none)) = d5192 p
  rw [sub7518, sub7753]
  rfl
theorem sub7755 (p : Pattern) : d2115 (change p 204 none) = d5193 p := by
  change (if p 161 then d2114 (change p 204 none) else d2112 (change p 204 none)) = d5193 p
  rw [sub7754, sub7752]
  rfl
theorem sub7756 (p : Pattern) : d2116 (change p 204 none) = d5194 p := by
  change (if p 182 then d1906 (change p 204 none) else d117 (change p 204 none)) = d5194 p
  rw [sub7539, sub7552]
  rfl
theorem sub7757 (p : Pattern) : d2117 (change p 204 none) = d5195 p := by
  change (if p 163 then d2116 (change p 204 none) else d1973 (change p 204 none)) = d5195 p
  rw [sub7756, sub7609]
  rfl
theorem sub7758 (p : Pattern) : d2118 (change p 204 none) = d5196 p := by
  change (if p 162 then d2092 (change p 204 none) else d2117 (change p 204 none)) = d5196 p
  rw [sub7732, sub7757]
  rfl
theorem sub7759 (p : Pattern) : d2119 (change p 204 none) = d229 p := by
  change (if p 182 then d12 (change p 204 none) else d121 (change p 204 none)) = d229 p
  rw [sub7260, sub7610]
  rfl
theorem sub7760 (p : Pattern) : d2120 (change p 204 none) = d230 p := by
  change (if p 163 then d12 (change p 204 none) else d2119 (change p 204 none)) = d230 p
  rw [sub7260, sub7759]
  rfl
theorem sub7761 (p : Pattern) : d2121 (change p 204 none) = d231 p := by
  change (if p 162 then d12 (change p 204 none) else d2120 (change p 204 none)) = d231 p
  rw [sub7260, sub7760]
  rfl
theorem sub7762 (p : Pattern) : d2122 (change p 204 none) = d5197 p := by
  change (if p 161 then d2121 (change p 204 none) else d2118 (change p 204 none)) = d5197 p
  rw [sub7761, sub7758]
  rfl
theorem sub7763 (p : Pattern) : d2123 (change p 204 none) = d5198 p := by
  change (if p 160 then d2122 (change p 204 none) else d2115 (change p 204 none)) = d5198 p
  rw [sub7762, sub7755]
  rfl
theorem sub7764 (p : Pattern) : d2124 (change p 204 none) = d2124 p := by
  change (if p 225 then d1895 (change p 204 none) else d116 (change p 204 none)) = d2124 p
  rw [sub7526, sub7521]
  rfl
theorem sub7765 (p : Pattern) : d2125 (change p 204 none) = d2125 p := by
  change (if p 224 then d1895 (change p 204 none) else d2124 (change p 204 none)) = d2125 p
  rw [sub7526, sub7764]
  rfl
theorem sub7766 (p : Pattern) : d2126 (change p 204 none) = d2125 p := by
  change d2125 (change p 204 none) = d2125 p
  exact sub7765 p
theorem sub7767 (p : Pattern) : d2127 (change p 204 none) = d5199 p := by
  change (if p 182 then d2126 (change p 204 none) else d117 (change p 204 none)) = d5199 p
  rw [sub7766, sub7552]
  rfl
theorem sub7768 (p : Pattern) : d2128 (change p 204 none) = d5200 p := by
  change (if p 163 then d2127 (change p 204 none) else d2110 (change p 204 none)) = d5200 p
  rw [sub7767, sub7750]
  rfl
theorem sub7769 (p : Pattern) : d2129 (change p 204 none) = d2129 p := by
  change (if p 225 then d1964 (change p 204 none) else d107 (change p 204 none)) = d2129 p
  rw [sub7599, sub7506]
  rfl
theorem sub7770 (p : Pattern) : d2130 (change p 204 none) = d2130 p := by
  change (if p 224 then d1964 (change p 204 none) else d2129 (change p 204 none)) = d2130 p
  rw [sub7599, sub7769]
  rfl
theorem sub7771 (p : Pattern) : d2131 (change p 204 none) = d2130 p := by
  change d2130 (change p 204 none) = d2130 p
  exact sub7770 p
theorem sub7772 (p : Pattern) : d2132 (change p 204 none) = d5201 p := by
  change (if p 182 then d2131 (change p 204 none) else d108 (change p 204 none)) = d5201 p
  rw [sub7771, sub7507]
  rfl
theorem sub7773 (p : Pattern) : d2133 (change p 204 none) = d5202 p := by
  change (if p 163 then d12 (change p 204 none) else d2132 (change p 204 none)) = d5202 p
  rw [sub7260, sub7772]
  rfl
theorem sub7774 (p : Pattern) : d2134 (change p 204 none) = d5203 p := by
  change (if p 162 then d2133 (change p 204 none) else d2128 (change p 204 none)) = d5203 p
  rw [sub7773, sub7768]
  rfl
theorem sub7775 (p : Pattern) : d2135 (change p 204 none) = d2135 p := by
  change (if p 225 then d1961 (change p 204 none) else d1964 (change p 204 none)) = d2135 p
  rw [sub7596, sub7599]
  rfl
theorem sub7776 (p : Pattern) : d2136 (change p 204 none) = d2136 p := by
  change (if p 224 then d2135 (change p 204 none) else d1962 (change p 204 none)) = d2136 p
  rw [sub7775, sub7597]
  rfl
theorem sub7777 (p : Pattern) : d2137 (change p 204 none) = d2136 p := by
  change d2136 (change p 204 none) = d2136 p
  exact sub7776 p
theorem sub7778 (p : Pattern) : d2138 (change p 204 none) = d5204 p := by
  change (if p 182 then d2137 (change p 204 none) else d108 (change p 204 none)) = d5204 p
  rw [sub7777, sub7507]
  rfl
theorem sub7779 (p : Pattern) : d2139 (change p 204 none) = d5205 p := by
  change (if p 163 then d12 (change p 204 none) else d2138 (change p 204 none)) = d5205 p
  rw [sub7260, sub7778]
  rfl
theorem sub7780 (p : Pattern) : d2140 (change p 204 none) = d5206 p := by
  change (if p 162 then d12 (change p 204 none) else d2139 (change p 204 none)) = d5206 p
  rw [sub7260, sub7779]
  rfl
theorem sub7781 (p : Pattern) : d2141 (change p 204 none) = d5207 p := by
  change (if p 161 then d2140 (change p 204 none) else d2134 (change p 204 none)) = d5207 p
  rw [sub7780, sub7774]
  rfl
theorem sub7782 (p : Pattern) : d2142 (change p 204 none) = d5208 p := by
  change (if p 182 then d1906 (change p 204 none) else d108 (change p 204 none)) = d5208 p
  rw [sub7539, sub7507]
  rfl
theorem sub7783 (p : Pattern) : d2143 (change p 204 none) = d5209 p := by
  change (if p 163 then d1910 (change p 204 none) else d2142 (change p 204 none)) = d5209 p
  rw [sub7543, sub7782]
  rfl
theorem sub7784 (p : Pattern) : d2144 (change p 204 none) = d5210 p := by
  change (if p 162 then d2120 (change p 204 none) else d2143 (change p 204 none)) = d5210 p
  rw [sub7760, sub7783]
  rfl
theorem sub7785 (p : Pattern) : d2145 (change p 204 none) = d237 p := by
  change (if p 162 then d12 (change p 204 none) else d528 (change p 204 none)) = d237 p
  rw [sub7260, sub7343]
  rfl
theorem sub7786 (p : Pattern) : d2146 (change p 204 none) = d5211 p := by
  change (if p 161 then d2145 (change p 204 none) else d2144 (change p 204 none)) = d5211 p
  rw [sub7785, sub7784]
  rfl
theorem sub7787 (p : Pattern) : d2147 (change p 204 none) = d5212 p := by
  change (if p 160 then d2146 (change p 204 none) else d2141 (change p 204 none)) = d5212 p
  rw [sub7786, sub7781]
  rfl
theorem sub7788 (p : Pattern) : d2148 (change p 204 none) = d5213 p := by
  change (if p 141 then d2147 (change p 204 none) else d2123 (change p 204 none)) = d5213 p
  rw [sub7787, sub7763]
  rfl
theorem sub7789 (p : Pattern) : d2149 (change p 204 none) = d5214 p := by
  change (if p 163 then d1959 (change p 204 none) else d1953 (change p 204 none)) = d5214 p
  rw [sub7594, sub7588]
  rfl
theorem sub7790 (p : Pattern) : d2150 (change p 204 none) = d5215 p := by
  change (if p 163 then d1756 (change p 204 none) else d1973 (change p 204 none)) = d5215 p
  rw [sub7368, sub7609]
  rfl
theorem sub7791 (p : Pattern) : d2151 (change p 204 none) = d5216 p := by
  change (if p 162 then d2150 (change p 204 none) else d2149 (change p 204 none)) = d5216 p
  rw [sub7790, sub7789]
  rfl
theorem sub7792 (p : Pattern) : d2152 (change p 204 none) = d5217 p := by
  change (if p 161 then d1983 (change p 204 none) else d2151 (change p 204 none)) = d5217 p
  rw [sub7620, sub7791]
  rfl
theorem sub7793 (p : Pattern) : d2153 (change p 204 none) = d5218 p := by
  change (if p 160 then d1987 (change p 204 none) else d2152 (change p 204 none)) = d5218 p
  rw [sub7624, sub7792]
  rfl
theorem sub7794 (p : Pattern) : d2154 (change p 204 none) = d2154 p := by
  change (if p 247 then d11 (change p 204 none) else d3 (change p 204 none)) = d2154 p
  rw [sub7295, sub7493]
  rfl
theorem sub7795 (p : Pattern) : d2155 (change p 204 none) = d2155 p := by
  change (if p 246 then d39 (change p 204 none) else d2154 (change p 204 none)) = d2155 p
  rw [sub7297, sub7794]
  rfl
theorem sub7796 (p : Pattern) : d2156 (change p 204 none) = d2156 p := by
  change (if p 225 then d2155 (change p 204 none) else d1895 (change p 204 none)) = d2156 p
  rw [sub7795, sub7526]
  rfl
theorem sub7797 (p : Pattern) : d2157 (change p 204 none) = d2157 p := by
  change (if p 224 then d2156 (change p 204 none) else d1893 (change p 204 none)) = d2157 p
  rw [sub7796, sub7524]
  rfl
theorem sub7798 (p : Pattern) : d2158 (change p 204 none) = d2157 p := by
  change d2157 (change p 204 none) = d2157 p
  exact sub7797 p
theorem sub7799 (p : Pattern) : d2159 (change p 204 none) = d5219 p := by
  change (if p 182 then d2158 (change p 204 none) else d117 (change p 204 none)) = d5219 p
  rw [sub7798, sub7552]
  rfl
end NetHack.Sokoban22Refined85
