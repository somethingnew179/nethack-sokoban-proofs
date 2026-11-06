/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions13
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s2100 (pattern : Twelve) : d112 (change pattern 2 9) = d2272 pattern := by
  change (if pattern.d then d107 (change pattern 2 9) else d106 (change pattern 2 9)) = d2272 pattern
  rw [s2099, s2091]
  rfl
theorem s2101 (pattern : Twelve) : d346 (change pattern 2 9) = d2272 pattern := by
  change d112 (change pattern 2 9) = d2272 pattern
  exact s2100 pattern
theorem s2102 (pattern : Twelve) : d348 (change pattern 2 9) = d2273 pattern := by
  change (if pattern.g then d346 (change pattern 2 9) else d345 (change pattern 2 9)) = d2273 pattern
  rw [s2101, s2081]
  rfl
theorem s2103 (pattern : Twelve) : d347 (change pattern 2 9) = d2271 pattern := by
  change d110 (change pattern 2 9) = d2271 pattern
  exact s2080 pattern
theorem s2104 (pattern : Twelve) : d349 (change pattern 2 9) = d2273 pattern := by
  change (if pattern.g then d346 (change pattern 2 9) else d347 (change pattern 2 9)) = d2273 pattern
  rw [s2101, s2103]
  rfl
theorem s2105 (pattern : Twelve) : d350 (change pattern 2 9) = d2273 pattern := by
  change (if pattern.b then d349 (change pattern 2 9) else d348 (change pattern 2 9)) = d2273 pattern
  rw [s2104, s2102]
  simp only [ite_self]
theorem s2106 (pattern : Twelve) : d351 (change pattern 2 9) = d2273 pattern := by
  change (if pattern.a then d349 (change pattern 2 9) else d350 (change pattern 2 9)) = d2273 pattern
  rw [s2104, s2105]
  simp only [ite_self]
theorem s2107 (pattern : Twelve) : d814 (change pattern 2 9) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 2 9) else d7 (change pattern 2 9)) = d814 pattern
  rw [s2050, s2051]
  rfl
theorem s2108 (pattern : Twelve) : d818 (change pattern 2 9) = d818 pattern := by
  change (if pattern.i then d6 (change pattern 2 9) else d814 (change pattern 2 9)) = d818 pattern
  rw [s2045, s2107]
  rfl
theorem s2109 (pattern : Twelve) : d826 (change pattern 2 9) = d826 pattern := by
  change (if pattern.h then d818 (change pattern 2 9) else d34 (change pattern 2 9)) = d826 pattern
  rw [s2108, s2063]
  rfl
theorem s2110 (pattern : Twelve) : d840 (change pattern 2 9) = d840 pattern := by
  change (if pattern.f then d826 (change pattern 2 9) else d56 (change pattern 2 9)) = d840 pattern
  rw [s2109, s2073]
  rfl
theorem s2111 (pattern : Twelve) : d827 (change pattern 2 9) = d827 pattern := by
  change (if pattern.h then d36 (change pattern 2 9) else d34 (change pattern 2 9)) = d827 pattern
  rw [s2074, s2063]
  rfl
theorem s2112 (pattern : Twelve) : d16 (change pattern 2 9) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 2 9) else d2 (change pattern 2 9)) = d16 pattern
  rw [s2044, s2039]
  rfl
theorem s2113 (pattern : Twelve) : d25 (change pattern 2 9) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 2 9) else d16 (change pattern 2 9)) = d25 pattern
  rw [s2043, s2112]
  rfl
theorem s2114 (pattern : Twelve) : d817 (change pattern 2 9) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 2 9) else d19 (change pattern 2 9)) = d817 pattern
  rw [s2113, s2066]
  rfl
theorem s2115 (pattern : Twelve) : d42 (change pattern 2 9) = d42 pattern := by
  change (if pattern.i then d6 (change pattern 2 9) else d25 (change pattern 2 9)) = d42 pattern
  rw [s2045, s2113]
  rfl
theorem s2116 (pattern : Twelve) : d825 (change pattern 2 9) = d825 pattern := by
  change (if pattern.h then d42 (change pattern 2 9) else d817 (change pattern 2 9)) = d825 pattern
  rw [s2115, s2114]
  rfl
theorem s2117 (pattern : Twelve) : d841 (change pattern 2 9) = d841 pattern := by
  change (if pattern.f then d825 (change pattern 2 9) else d827 (change pattern 2 9)) = d841 pattern
  rw [s2116, s2111]
  rfl
theorem s2118 (pattern : Twelve) : d854 (change pattern 2 9) = d854 pattern := by
  change (if pattern.e then d841 (change pattern 2 9) else d840 (change pattern 2 9)) = d854 pattern
  rw [s2117, s2110]
  rfl
theorem s2119 (pattern : Twelve) : d861 (change pattern 2 9) = d854 pattern := by
  change d854 (change pattern 2 9) = d854 pattern
  exact s2118 pattern
theorem s2120 (pattern : Twelve) : d1011 (change pattern 2 9) = d854 pattern := by
  change d861 (change pattern 2 9) = d854 pattern
  exact s2119 pattern
theorem s2121 (pattern : Twelve) : d832 (change pattern 2 9) = d832 pattern := by
  change (if pattern.h then d45 (change pattern 2 9) else d34 (change pattern 2 9)) = d832 pattern
  rw [s2092, s2063]
  rfl
theorem s2122 (pattern : Twelve) : d847 (change pattern 2 9) = d847 pattern := by
  change (if pattern.f then d832 (change pattern 2 9) else d56 (change pattern 2 9)) = d847 pattern
  rw [s2121, s2073]
  rfl
theorem s2123 (pattern : Twelve) : d833 (change pattern 2 9) = d833 pattern := by
  change (if pattern.h then d39 (change pattern 2 9) else d34 (change pattern 2 9)) = d833 pattern
  rw [s2095, s2063]
  rfl
theorem s2124 (pattern : Twelve) : d848 (change pattern 2 9) = d848 pattern := by
  change (if pattern.f then d825 (change pattern 2 9) else d833 (change pattern 2 9)) = d848 pattern
  rw [s2116, s2123]
  rfl
theorem s2125 (pattern : Twelve) : d858 (change pattern 2 9) = d858 pattern := by
  change (if pattern.e then d848 (change pattern 2 9) else d847 (change pattern 2 9)) = d858 pattern
  rw [s2124, s2122]
  rfl
theorem s2126 (pattern : Twelve) : d864 (change pattern 2 9) = d858 pattern := by
  change d858 (change pattern 2 9) = d858 pattern
  exact s2125 pattern
theorem s2127 (pattern : Twelve) : d1012 (change pattern 2 9) = d858 pattern := by
  change d864 (change pattern 2 9) = d858 pattern
  exact s2126 pattern
theorem s2128 (pattern : Twelve) : d1014 (change pattern 2 9) = d2274 pattern := by
  change (if pattern.g then d1012 (change pattern 2 9) else d1011 (change pattern 2 9)) = d2274 pattern
  rw [s2127, s2120]
  rfl
theorem s2129 (pattern : Twelve) : d1013 (change pattern 2 9) = d854 pattern := by
  change d861 (change pattern 2 9) = d854 pattern
  exact s2119 pattern
theorem s2130 (pattern : Twelve) : d1015 (change pattern 2 9) = d2274 pattern := by
  change (if pattern.g then d1012 (change pattern 2 9) else d1013 (change pattern 2 9)) = d2274 pattern
  rw [s2127, s2129]
  rfl
theorem s2131 (pattern : Twelve) : d1016 (change pattern 2 9) = d2274 pattern := by
  change (if pattern.b then d1015 (change pattern 2 9) else d1014 (change pattern 2 9)) = d2274 pattern
  rw [s2130, s2128]
  simp only [ite_self]
theorem s2132 (pattern : Twelve) : d1017 (change pattern 2 9) = d2274 pattern := by
  change (if pattern.a then d1015 (change pattern 2 9) else d1016 (change pattern 2 9)) = d2274 pattern
  rw [s2130, s2131]
  simp only [ite_self]
theorem s2133 (pattern : Twelve) : d8 (change pattern 2 9) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 2 9) else d1 (change pattern 2 9)) = d8 pattern
  rw [s2039, s2050]
  rfl
theorem s2134 (pattern : Twelve) : d1275 (change pattern 2 9) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 2 9) else d7 (change pattern 2 9)) = d1275 pattern
  rw [s2133, s2051]
  rfl
theorem s2135 (pattern : Twelve) : d117 (change pattern 2 9) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 2 9) else d3 (change pattern 2 9)) = d117 pattern
  rw [s2044, s2041]
  rfl
theorem s2136 (pattern : Twelve) : d1276 (change pattern 2 9) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 2 9) else d9 (change pattern 2 9)) = d1276 pattern
  rw [s2135, s2061]
  rfl
theorem s2137 (pattern : Twelve) : d1279 (change pattern 2 9) = d1279 pattern := by
  change (if pattern.i then d1276 (change pattern 2 9) else d1275 (change pattern 2 9)) = d1279 pattern
  rw [s2136, s2134]
  rfl
theorem s2138 (pattern : Twelve) : d872 (change pattern 2 9) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 2 9) else d1 (change pattern 2 9)) = d872 pattern
  rw [s2133, s2050]
  rfl
theorem s2139 (pattern : Twelve) : d1280 (change pattern 2 9) = d1280 pattern := by
  change (if pattern.i then d6 (change pattern 2 9) else d872 (change pattern 2 9)) = d1280 pattern
  rw [s2045, s2138]
  rfl
theorem s2140 (pattern : Twelve) : d1285 (change pattern 2 9) = d1285 pattern := by
  change (if pattern.h then d1280 (change pattern 2 9) else d1279 (change pattern 2 9)) = d1285 pattern
  rw [s2139, s2137]
  rfl
theorem s2141 (pattern : Twelve) : d1295 (change pattern 2 9) = d1295 pattern := by
  change (if pattern.f then d1285 (change pattern 2 9) else d827 (change pattern 2 9)) = d1295 pattern
  rw [s2140, s2111]
  rfl
theorem s2142 (pattern : Twelve) : d1286 (change pattern 2 9) = d1286 pattern := by
  change (if pattern.h then d29 (change pattern 2 9) else d817 (change pattern 2 9)) = d1286 pattern
  rw [s2067, s2114]
  rfl
theorem s2143 (pattern : Twelve) : d1296 (change pattern 2 9) = d1296 pattern := by
  change (if pattern.f then d6 (change pattern 2 9) else d1286 (change pattern 2 9)) = d1296 pattern
  rw [s2045, s2142]
  rfl
theorem s2144 (pattern : Twelve) : d1306 (change pattern 2 9) = d1306 pattern := by
  change (if pattern.e then d1296 (change pattern 2 9) else d1295 (change pattern 2 9)) = d1306 pattern
  rw [s2143, s2141]
  rfl
theorem s2145 (pattern : Twelve) : d1313 (change pattern 2 9) = d1306 pattern := by
  change d1306 (change pattern 2 9) = d1306 pattern
  exact s2144 pattern
theorem s2146 (pattern : Twelve) : d1428 (change pattern 2 9) = d1306 pattern := by
  change d1313 (change pattern 2 9) = d1306 pattern
  exact s2145 pattern
theorem s2147 (pattern : Twelve) : d1290 (change pattern 2 9) = d1290 pattern := by
  change (if pattern.h then d40 (change pattern 2 9) else d817 (change pattern 2 9)) = d1290 pattern
  rw [s2087, s2114]
  rfl
theorem s2148 (pattern : Twelve) : d1302 (change pattern 2 9) = d1302 pattern := by
  change (if pattern.f then d6 (change pattern 2 9) else d1290 (change pattern 2 9)) = d1302 pattern
  rw [s2045, s2147]
  rfl
theorem s2149 (pattern : Twelve) : d1310 (change pattern 2 9) = d1310 pattern := by
  change (if pattern.e then d1302 (change pattern 2 9) else d1295 (change pattern 2 9)) = d1310 pattern
  rw [s2148, s2141]
  rfl
theorem s2150 (pattern : Twelve) : d1316 (change pattern 2 9) = d1310 pattern := by
  change d1310 (change pattern 2 9) = d1310 pattern
  exact s2149 pattern
theorem s2151 (pattern : Twelve) : d1429 (change pattern 2 9) = d1310 pattern := by
  change d1316 (change pattern 2 9) = d1310 pattern
  exact s2150 pattern
theorem s2152 (pattern : Twelve) : d1431 (change pattern 2 9) = d2275 pattern := by
  change (if pattern.g then d1429 (change pattern 2 9) else d1428 (change pattern 2 9)) = d2275 pattern
  rw [s2151, s2146]
  rfl
theorem s2153 (pattern : Twelve) : d1430 (change pattern 2 9) = d1306 pattern := by
  change d1313 (change pattern 2 9) = d1306 pattern
  exact s2145 pattern
theorem s2154 (pattern : Twelve) : d1432 (change pattern 2 9) = d2275 pattern := by
  change (if pattern.g then d1429 (change pattern 2 9) else d1430 (change pattern 2 9)) = d2275 pattern
  rw [s2151, s2153]
  rfl
theorem s2155 (pattern : Twelve) : d1433 (change pattern 2 9) = d2275 pattern := by
  change (if pattern.b then d1432 (change pattern 2 9) else d1431 (change pattern 2 9)) = d2275 pattern
  rw [s2154, s2152]
  simp only [ite_self]
theorem s2156 (pattern : Twelve) : d1434 (change pattern 2 9) = d2275 pattern := by
  change (if pattern.a then d1432 (change pattern 2 9) else d1433 (change pattern 2 9)) = d2275 pattern
  rw [s2154, s2155]
  simp only [ite_self]
theorem s2157 (pattern : Twelve) : d1324 (change pattern 2 9) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 2 9) else d11 (change pattern 2 9)) = d1324 pattern
  rw [s2112, s2065]
  rfl
theorem s2158 (pattern : Twelve) : d1644 (change pattern 2 9) = d1644 pattern := by
  change (if pattern.i then d20 (change pattern 2 9) else d1324 (change pattern 2 9)) = d1644 pattern
  rw [s2047, s2157]
  rfl
theorem s2159 (pattern : Twelve) : d1645 (change pattern 2 9) = d1645 pattern := by
  change (if pattern.i then d6 (change pattern 2 9) else d1324 (change pattern 2 9)) = d1645 pattern
  rw [s2045, s2157]
  rfl
theorem s2160 (pattern : Twelve) : d1647 (change pattern 2 9) = d1647 pattern := by
  change (if pattern.h then d1645 (change pattern 2 9) else d1644 (change pattern 2 9)) = d1647 pattern
  rw [s2159, s2158]
  rfl
theorem s2161 (pattern : Twelve) : d1651 (change pattern 2 9) = d1651 pattern := by
  change (if pattern.f then d1647 (change pattern 2 9) else d1286 (change pattern 2 9)) = d1651 pattern
  rw [s2160, s2142]
  rfl
theorem s2162 (pattern : Twelve) : d821 (change pattern 2 9) = d821 pattern := by
  change (if pattern.i then d21 (change pattern 2 9) else d25 (change pattern 2 9)) = d821 pattern
  rw [s2054, s2113]
  rfl
theorem s2163 (pattern : Twelve) : d1289 (change pattern 2 9) = d1289 pattern := by
  change (if pattern.h then d42 (change pattern 2 9) else d821 (change pattern 2 9)) = d1289 pattern
  rw [s2115, s2162]
  rfl
theorem s2164 (pattern : Twelve) : d1300 (change pattern 2 9) = d1300 pattern := by
  change (if pattern.f then d6 (change pattern 2 9) else d1289 (change pattern 2 9)) = d1300 pattern
  rw [s2045, s2163]
  rfl
theorem s2165 (pattern : Twelve) : d1657 (change pattern 2 9) = d1657 pattern := by
  change (if pattern.e then d1300 (change pattern 2 9) else d1651 (change pattern 2 9)) = d1657 pattern
  rw [s2164, s2161]
  rfl
theorem s2166 (pattern : Twelve) : d1660 (change pattern 2 9) = d1657 pattern := by
  change d1657 (change pattern 2 9) = d1657 pattern
  exact s2165 pattern
theorem s2167 (pattern : Twelve) : d1714 (change pattern 2 9) = d1657 pattern := by
  change d1660 (change pattern 2 9) = d1657 pattern
  exact s2166 pattern
theorem s2168 (pattern : Twelve) : d0 (change pattern 2 12) = d0 pattern := by
  rfl
theorem s2169 (pattern : Twelve) : d1 (change pattern 2 12) = d1 pattern := by
  rfl
theorem s2170 (pattern : Twelve) : d7 (change pattern 2 12) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 2 12) else d0 (change pattern 2 12)) = d7 pattern
  rw [s2169, s2168]
  rfl
theorem s2171 (pattern : Twelve) : d17 (change pattern 2 12) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 2 12) else d0 (change pattern 2 12)) = d17 pattern
  rw [s2170, s2168]
  rfl
theorem s2172 (pattern : Twelve) : d27 (change pattern 2 12) = d27 pattern := by
  change (if pattern.i then d1 (change pattern 2 12) else d17 (change pattern 2 12)) = d27 pattern
  rw [s2169, s2171]
  rfl
theorem s2173 (pattern : Twelve) : d814 (change pattern 2 12) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 2 12) else d7 (change pattern 2 12)) = d814 pattern
  rw [s2169, s2170]
  rfl
theorem s2174 (pattern : Twelve) : d816 (change pattern 2 12) = d816 pattern := by
  change (if pattern.i then d1 (change pattern 2 12) else d814 (change pattern 2 12)) = d816 pattern
  rw [s2169, s2173]
  rfl
theorem s2175 (pattern : Twelve) : d824 (change pattern 2 12) = d824 pattern := by
  change (if pattern.h then d816 (change pattern 2 12) else d27 (change pattern 2 12)) = d824 pattern
  rw [s2174, s2172]
  rfl
theorem s2176 (pattern : Twelve) : d838 (change pattern 2 12) = d838 pattern := by
  change (if pattern.f then d824 (change pattern 2 12) else d0 (change pattern 2 12)) = d838 pattern
  rw [s2175, s2168]
  rfl
theorem s2177 (pattern : Twelve) : d2 (change pattern 2 12) = d2 pattern := by
  rfl
theorem s2178 (pattern : Twelve) : d10 (change pattern 2 12) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 2 12) else d0 (change pattern 2 12)) = d10 pattern
  rw [s2177, s2168]
  rfl
theorem s2179 (pattern : Twelve) : d3 (change pattern 2 12) = d3 pattern := by
  rfl
theorem s2180 (pattern : Twelve) : d11 (change pattern 2 12) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 2 12) else d1 (change pattern 2 12)) = d11 pattern
  rw [s2179, s2169]
  rfl
theorem s2181 (pattern : Twelve) : d19 (change pattern 2 12) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 2 12) else d10 (change pattern 2 12)) = d19 pattern
  rw [s2180, s2178]
  rfl
theorem s2182 (pattern : Twelve) : d4 (change pattern 2 12) = d4 pattern := by
  rfl
theorem s2183 (pattern : Twelve) : d16 (change pattern 2 12) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 2 12) else d2 (change pattern 2 12)) = d16 pattern
  rw [s2182, s2177]
  rfl
theorem s2184 (pattern : Twelve) : d5 (change pattern 2 12) = d5 pattern := by
  rfl
theorem s2185 (pattern : Twelve) : d12 (change pattern 2 12) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 2 12) else d3 (change pattern 2 12)) = d12 pattern
  rw [s2184, s2179]
  rfl
theorem s2186 (pattern : Twelve) : d25 (change pattern 2 12) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 2 12) else d16 (change pattern 2 12)) = d25 pattern
  rw [s2185, s2183]
  rfl
theorem s2187 (pattern : Twelve) : d817 (change pattern 2 12) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 2 12) else d19 (change pattern 2 12)) = d817 pattern
  rw [s2186, s2181]
  rfl
theorem s2188 (pattern : Twelve) : d6 (change pattern 2 12) = d6 pattern := by
  rfl
theorem s2189 (pattern : Twelve) : d42 (change pattern 2 12) = d42 pattern := by
  change (if pattern.i then d6 (change pattern 2 12) else d25 (change pattern 2 12)) = d42 pattern
  rw [s2188, s2186]
  rfl
theorem s2190 (pattern : Twelve) : d825 (change pattern 2 12) = d825 pattern := by
  change (if pattern.h then d42 (change pattern 2 12) else d817 (change pattern 2 12)) = d825 pattern
  rw [s2189, s2187]
  rfl
theorem s2191 (pattern : Twelve) : d839 (change pattern 2 12) = d839 pattern := by
  change (if pattern.f then d825 (change pattern 2 12) else d17 (change pattern 2 12)) = d839 pattern
  rw [s2190, s2171]
  rfl
theorem s2192 (pattern : Twelve) : d853 (change pattern 2 12) = d853 pattern := by
  change (if pattern.e then d839 (change pattern 2 12) else d838 (change pattern 2 12)) = d853 pattern
  rw [s2191, s2176]
  rfl
theorem s2193 (pattern : Twelve) : d30 (change pattern 2 12) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 2 12) else d0 (change pattern 2 12)) = d30 pattern
  rw [s2177, s2168]
  rfl
theorem s2194 (pattern : Twelve) : d35 (change pattern 2 12) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 2 12) else d0 (change pattern 2 12)) = d35 pattern
  rw [s2188, s2168]
  rfl
theorem s2195 (pattern : Twelve) : d56 (change pattern 2 12) = d56 pattern := by
  change (if pattern.h then d35 (change pattern 2 12) else d30 (change pattern 2 12)) = d56 pattern
  rw [s2194, s2193]
  rfl
theorem s2196 (pattern : Twelve) : d9 (change pattern 2 12) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 2 12) else d2 (change pattern 2 12)) = d9 pattern
  rw [s2179, s2177]
  rfl
theorem s2197 (pattern : Twelve) : d23 (change pattern 2 12) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 2 12) else d2 (change pattern 2 12)) = d23 pattern
  rw [s2196, s2177]
  rfl
theorem s2198 (pattern : Twelve) : d34 (change pattern 2 12) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 2 12) else d17 (change pattern 2 12)) = d34 pattern
  rw [s2197, s2171]
  rfl
theorem s2199 (pattern : Twelve) : d818 (change pattern 2 12) = d818 pattern := by
  change (if pattern.i then d6 (change pattern 2 12) else d814 (change pattern 2 12)) = d818 pattern
  rw [s2188, s2173]
  rfl
theorem s2200 (pattern : Twelve) : d826 (change pattern 2 12) = d826 pattern := by
  change (if pattern.h then d818 (change pattern 2 12) else d34 (change pattern 2 12)) = d826 pattern
  rw [s2199, s2198]
  rfl
theorem s2201 (pattern : Twelve) : d840 (change pattern 2 12) = d840 pattern := by
  change (if pattern.f then d826 (change pattern 2 12) else d56 (change pattern 2 12)) = d840 pattern
  rw [s2200, s2195]
  rfl
theorem s2202 (pattern : Twelve) : d36 (change pattern 2 12) = d36 pattern := by
  change (if pattern.i then d6 (change pattern 2 12) else d17 (change pattern 2 12)) = d36 pattern
  rw [s2188, s2171]
  rfl
theorem s2203 (pattern : Twelve) : d827 (change pattern 2 12) = d827 pattern := by
  change (if pattern.h then d36 (change pattern 2 12) else d34 (change pattern 2 12)) = d827 pattern
  rw [s2202, s2198]
  rfl
theorem s2204 (pattern : Twelve) : d841 (change pattern 2 12) = d841 pattern := by
  change (if pattern.f then d825 (change pattern 2 12) else d827 (change pattern 2 12)) = d841 pattern
  rw [s2190, s2203]
  rfl
theorem s2205 (pattern : Twelve) : d854 (change pattern 2 12) = d854 pattern := by
  change (if pattern.e then d841 (change pattern 2 12) else d840 (change pattern 2 12)) = d854 pattern
  rw [s2204, s2201]
  rfl
theorem s2206 (pattern : Twelve) : d861 (change pattern 2 12) = d861 pattern := by
  change (if pattern.j then d854 (change pattern 2 12) else d853 (change pattern 2 12)) = d861 pattern
  rw [s2205, s2192]
  rfl
theorem s2207 (pattern : Twelve) : d1011 (change pattern 2 12) = d861 pattern := by
  change d861 (change pattern 2 12) = d861 pattern
  exact s2206 pattern
theorem s2208 (pattern : Twelve) : d823 (change pattern 2 12) = d823 pattern := by
  change (if pattern.i then d2 (change pattern 2 12) else d17 (change pattern 2 12)) = d823 pattern
  rw [s2177, s2171]
  rfl
theorem s2209 (pattern : Twelve) : d846 (change pattern 2 12) = d846 pattern := by
  change (if pattern.f then d825 (change pattern 2 12) else d823 (change pattern 2 12)) = d846 pattern
  rw [s2190, s2208]
  rfl
theorem s2210 (pattern : Twelve) : d857 (change pattern 2 12) = d857 pattern := by
  change (if pattern.e then d846 (change pattern 2 12) else d838 (change pattern 2 12)) = d857 pattern
  rw [s2209, s2176]
  rfl
theorem s2211 (pattern : Twelve) : d45 (change pattern 2 12) = d45 pattern := by
  change (if pattern.i then d6 (change pattern 2 12) else d1 (change pattern 2 12)) = d45 pattern
  rw [s2188, s2169]
  rfl
theorem s2212 (pattern : Twelve) : d832 (change pattern 2 12) = d832 pattern := by
  change (if pattern.h then d45 (change pattern 2 12) else d34 (change pattern 2 12)) = d832 pattern
  rw [s2211, s2198]
  rfl
theorem s2213 (pattern : Twelve) : d847 (change pattern 2 12) = d847 pattern := by
  change (if pattern.f then d832 (change pattern 2 12) else d56 (change pattern 2 12)) = d847 pattern
  rw [s2212, s2195]
  rfl
theorem s2214 (pattern : Twelve) : d39 (change pattern 2 12) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 2 12) else d2 (change pattern 2 12)) = d39 pattern
  rw [s2188, s2177]
  rfl
theorem s2215 (pattern : Twelve) : d833 (change pattern 2 12) = d833 pattern := by
  change (if pattern.h then d39 (change pattern 2 12) else d34 (change pattern 2 12)) = d833 pattern
  rw [s2214, s2198]
  rfl
theorem s2216 (pattern : Twelve) : d848 (change pattern 2 12) = d848 pattern := by
  change (if pattern.f then d825 (change pattern 2 12) else d833 (change pattern 2 12)) = d848 pattern
  rw [s2190, s2215]
  rfl
theorem s2217 (pattern : Twelve) : d858 (change pattern 2 12) = d858 pattern := by
  change (if pattern.e then d848 (change pattern 2 12) else d847 (change pattern 2 12)) = d858 pattern
  rw [s2216, s2213]
  rfl
theorem s2218 (pattern : Twelve) : d864 (change pattern 2 12) = d864 pattern := by
  change (if pattern.j then d858 (change pattern 2 12) else d857 (change pattern 2 12)) = d864 pattern
  rw [s2217, s2210]
  rfl
theorem s2219 (pattern : Twelve) : d1012 (change pattern 2 12) = d864 pattern := by
  change d864 (change pattern 2 12) = d864 pattern
  exact s2218 pattern
theorem s2220 (pattern : Twelve) : d1014 (change pattern 2 12) = d2268 pattern := by
  change (if pattern.g then d1012 (change pattern 2 12) else d1011 (change pattern 2 12)) = d2268 pattern
  rw [s2219, s2207]
  rfl
theorem s2221 (pattern : Twelve) : d1013 (change pattern 2 12) = d861 pattern := by
  change d861 (change pattern 2 12) = d861 pattern
  exact s2206 pattern
theorem s2222 (pattern : Twelve) : d1015 (change pattern 2 12) = d2268 pattern := by
  change (if pattern.g then d1012 (change pattern 2 12) else d1013 (change pattern 2 12)) = d2268 pattern
  rw [s2219, s2221]
  rfl
theorem s2223 (pattern : Twelve) : d1016 (change pattern 2 12) = d2268 pattern := by
  change (if pattern.b then d1015 (change pattern 2 12) else d1014 (change pattern 2 12)) = d2268 pattern
  rw [s2222, s2220]
  simp only [ite_self]
theorem s2224 (pattern : Twelve) : d1017 (change pattern 2 12) = d2268 pattern := by
  change (if pattern.a then d1015 (change pattern 2 12) else d1016 (change pattern 2 12)) = d2268 pattern
  rw [s2222, s2223]
  simp only [ite_self]
theorem s2225 (pattern : Twelve) : d8 (change pattern 2 12) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 2 12) else d1 (change pattern 2 12)) = d8 pattern
  rw [s2177, s2169]
  rfl
theorem s2226 (pattern : Twelve) : d1275 (change pattern 2 12) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 2 12) else d7 (change pattern 2 12)) = d1275 pattern
  rw [s2225, s2170]
  rfl
theorem s2227 (pattern : Twelve) : d872 (change pattern 2 12) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 2 12) else d1 (change pattern 2 12)) = d872 pattern
  rw [s2225, s2169]
  rfl
theorem s2228 (pattern : Twelve) : d1278 (change pattern 2 12) = d1278 pattern := by
  change (if pattern.i then d872 (change pattern 2 12) else d1275 (change pattern 2 12)) = d1278 pattern
  rw [s2227, s2226]
  rfl
theorem s2229 (pattern : Twelve) : d1284 (change pattern 2 12) = d1284 pattern := by
  change (if pattern.h then d872 (change pattern 2 12) else d1278 (change pattern 2 12)) = d1284 pattern
  rw [s2227, s2228]
  rfl
theorem s2230 (pattern : Twelve) : d1293 (change pattern 2 12) = d1293 pattern := by
  change (if pattern.f then d1284 (change pattern 2 12) else d17 (change pattern 2 12)) = d1293 pattern
  rw [s2229, s2171]
  rfl
theorem s2231 (pattern : Twelve) : d1294 (change pattern 2 12) = d1294 pattern := by
  change (if pattern.f then d6 (change pattern 2 12) else d19 (change pattern 2 12)) = d1294 pattern
  rw [s2188, s2181]
  rfl
theorem s2232 (pattern : Twelve) : d1305 (change pattern 2 12) = d1305 pattern := by
  change (if pattern.e then d1294 (change pattern 2 12) else d1293 (change pattern 2 12)) = d1305 pattern
  rw [s2231, s2230]
  rfl
theorem s2233 (pattern : Twelve) : d117 (change pattern 2 12) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 2 12) else d3 (change pattern 2 12)) = d117 pattern
  rw [s2182, s2179]
  rfl
theorem s2234 (pattern : Twelve) : d1276 (change pattern 2 12) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 2 12) else d9 (change pattern 2 12)) = d1276 pattern
  rw [s2233, s2196]
  rfl
theorem s2235 (pattern : Twelve) : d1279 (change pattern 2 12) = d1279 pattern := by
  change (if pattern.i then d1276 (change pattern 2 12) else d1275 (change pattern 2 12)) = d1279 pattern
  rw [s2234, s2226]
  rfl
theorem s2236 (pattern : Twelve) : d1280 (change pattern 2 12) = d1280 pattern := by
  change (if pattern.i then d6 (change pattern 2 12) else d872 (change pattern 2 12)) = d1280 pattern
  rw [s2188, s2227]
  rfl
theorem s2237 (pattern : Twelve) : d1285 (change pattern 2 12) = d1285 pattern := by
  change (if pattern.h then d1280 (change pattern 2 12) else d1279 (change pattern 2 12)) = d1285 pattern
  rw [s2236, s2235]
  rfl
theorem s2238 (pattern : Twelve) : d1295 (change pattern 2 12) = d1295 pattern := by
  change (if pattern.f then d1285 (change pattern 2 12) else d827 (change pattern 2 12)) = d1295 pattern
  rw [s2237, s2203]
  rfl
theorem s2239 (pattern : Twelve) : d29 (change pattern 2 12) = d29 pattern := by
  change (if pattern.i then d6 (change pattern 2 12) else d19 (change pattern 2 12)) = d29 pattern
  rw [s2188, s2181]
  rfl
theorem s2240 (pattern : Twelve) : d1286 (change pattern 2 12) = d1286 pattern := by
  change (if pattern.h then d29 (change pattern 2 12) else d817 (change pattern 2 12)) = d1286 pattern
  rw [s2239, s2187]
  rfl
theorem s2241 (pattern : Twelve) : d1296 (change pattern 2 12) = d1296 pattern := by
  change (if pattern.f then d6 (change pattern 2 12) else d1286 (change pattern 2 12)) = d1296 pattern
  rw [s2188, s2240]
  rfl
theorem s2242 (pattern : Twelve) : d1306 (change pattern 2 12) = d1306 pattern := by
  change (if pattern.e then d1296 (change pattern 2 12) else d1295 (change pattern 2 12)) = d1306 pattern
  rw [s2241, s2238]
  rfl
theorem s2243 (pattern : Twelve) : d1313 (change pattern 2 12) = d1313 pattern := by
  change (if pattern.j then d1306 (change pattern 2 12) else d1305 (change pattern 2 12)) = d1313 pattern
  rw [s2242, s2232]
  rfl
theorem s2244 (pattern : Twelve) : d1428 (change pattern 2 12) = d1313 pattern := by
  change d1313 (change pattern 2 12) = d1313 pattern
  exact s2243 pattern
theorem s2245 (pattern : Twelve) : d1283 (change pattern 2 12) = d1283 pattern := by
  change (if pattern.i then d23 (change pattern 2 12) else d19 (change pattern 2 12)) = d1283 pattern
  rw [s2197, s2181]
  rfl
theorem s2246 (pattern : Twelve) : d1301 (change pattern 2 12) = d1301 pattern := by
  change (if pattern.f then d6 (change pattern 2 12) else d1283 (change pattern 2 12)) = d1301 pattern
  rw [s2188, s2245]
  rfl
theorem s2247 (pattern : Twelve) : d1309 (change pattern 2 12) = d1309 pattern := by
  change (if pattern.e then d1301 (change pattern 2 12) else d1293 (change pattern 2 12)) = d1309 pattern
  rw [s2246, s2230]
  rfl
theorem s2248 (pattern : Twelve) : d40 (change pattern 2 12) = d40 pattern := by
  change (if pattern.i then d6 (change pattern 2 12) else d23 (change pattern 2 12)) = d40 pattern
  rw [s2188, s2197]
  rfl
theorem s2249 (pattern : Twelve) : d1290 (change pattern 2 12) = d1290 pattern := by
  change (if pattern.h then d40 (change pattern 2 12) else d817 (change pattern 2 12)) = d1290 pattern
  rw [s2248, s2187]
  rfl
end NetHack.Sokoban21.Diagram
