/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions16
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2040 (p : Pattern) : d5 (change p 160 (some 134)) = d5 p := by
  rfl
theorem sub2041 (p : Pattern) : d58 (change p 160 (some 134)) = d58 p := by
  change (if p 271 then d5 (change p 160 (some 134)) else d4 (change p 160 (some 134))) = d58 p
  rw [sub2040, sub2036]
  rfl
theorem sub2042 (p : Pattern) : d59 (change p 160 (some 134)) = d59 p := by
  change (if p 193 then d58 (change p 160 (some 134)) else d9 (change p 160 (some 134))) = d59 p
  rw [sub2041, sub2030]
  rfl
theorem sub2043 (p : Pattern) : d60 (change p 160 (some 134)) = d60 p := by
  change (if p 192 then d59 (change p 160 (some 134)) else d9 (change p 160 (some 134))) = d60 p
  rw [sub2042, sub2030]
  rfl
theorem sub2044 (p : Pattern) : d65 (change p 160 (some 134)) = d65 p := by
  change (if p 168 then d60 (change p 160 (some 134)) else d55 (change p 160 (some 134))) = d65 p
  rw [sub2043, sub2038]
  rfl
theorem sub2045 (p : Pattern) : d230 (change p 160 (some 134)) = d833 p := by
  change (if p 158 then d65 (change p 160 (some 134)) else d109 (change p 160 (some 134))) = d833 p
  rw [sub2044, sub2034]
  rfl
theorem sub2046 (p : Pattern) : d231 (change p 160 (some 134)) = d834 p := by
  change (if p 141 then d230 (change p 160 (some 134)) else d229 (change p 160 (some 134))) = d834 p
  rw [sub2045, sub2039]
  rfl
theorem sub2047 (p : Pattern) : d366 (change p 160 (some 134)) = d835 p := by
  change (if p 133 then d231 (change p 160 (some 134)) else d227 (change p 160 (some 134))) = d835 p
  rw [sub2046, sub2035]
  rfl
theorem sub2048 (p : Pattern) : d66 (change p 160 (some 134)) = d66 p := by
  change (if p 141 then d65 (change p 160 (some 134)) else d55 (change p 160 (some 134))) = d66 p
  rw [sub2044, sub2038]
  rfl
theorem sub2049 (p : Pattern) : d367 (change p 160 (some 134)) = d836 p := by
  change (if p 133 then d66 (change p 160 (some 134)) else d231 (change p 160 (some 134))) = d836 p
  rw [sub2048, sub2046]
  rfl
theorem sub2050 (p : Pattern) : d368 (change p 160 (some 134)) = d837 p := by
  change (if p 132 then d367 (change p 160 (some 134)) else d366 (change p 160 (some 134))) = d837 p
  rw [sub2049, sub2047]
  rfl
theorem sub2051 (p : Pattern) : d369 (change p 160 (some 134)) = d66 p := by
  change d66 (change p 160 (some 134)) = d66 p
  exact sub2048 p
theorem sub2052 (p : Pattern) : d370 (change p 160 (some 134)) = d66 p := by
  change d66 (change p 160 (some 134)) = d66 p
  exact sub2048 p
theorem sub2053 (p : Pattern) : d371 (change p 160 (some 134)) = d66 p := by
  change (if p 133 then d370 (change p 160 (some 134)) else d369 (change p 160 (some 134))) = d66 p
  rw [sub2052, sub2051]
  simp only [ite_self]
theorem sub2054 (p : Pattern) : d372 (change p 160 (some 134)) = d66 p := by
  change (if p 133 then d66 (change p 160 (some 134)) else d370 (change p 160 (some 134))) = d66 p
  rw [sub2048, sub2052]
  simp only [ite_self]
theorem sub2055 (p : Pattern) : d373 (change p 160 (some 134)) = d66 p := by
  change (if p 132 then d372 (change p 160 (some 134)) else d371 (change p 160 (some 134))) = d66 p
  rw [sub2054, sub2053]
  simp only [ite_self]
theorem sub2056 (p : Pattern) : d374 (change p 160 (some 134)) = d1173 p := by
  change (if p 108 then d373 (change p 160 (some 134)) else d368 (change p 160 (some 134))) = d1173 p
  rw [sub2055, sub2050]
  rfl
theorem sub2057 (p : Pattern) : d227 (change p 10000 none) = d227 p := by
  change (if p 141 then d109 (change p 10000 none) else d106 (change p 10000 none)) = d227 p
  rw [sub69, sub66]
  rfl
theorem sub2058 (p : Pattern) : d228 (change p 10000 none) = d228 p := by
  change (if p 134 then d227 (change p 10000 none) else d64 (change p 10000 none)) = d228 p
  rw [sub2057, sub23]
  rfl
theorem sub2059 (p : Pattern) : d229 (change p 10000 none) = d229 p := by
  change (if p 158 then d55 (change p 10000 none) else d106 (change p 10000 none)) = d229 p
  rw [sub6, sub66]
  rfl
theorem sub2060 (p : Pattern) : d230 (change p 10000 none) = d230 p := by
  change (if p 158 then d65 (change p 10000 none) else d109 (change p 10000 none)) = d230 p
  rw [sub24, sub69]
  rfl
theorem sub2061 (p : Pattern) : d231 (change p 10000 none) = d231 p := by
  change (if p 141 then d230 (change p 10000 none) else d229 (change p 10000 none)) = d231 p
  rw [sub2060, sub2059]
  rfl
theorem sub2062 (p : Pattern) : d232 (change p 10000 none) = d232 p := by
  change (if p 134 then d231 (change p 10000 none) else d70 (change p 10000 none)) = d232 p
  rw [sub2061, sub29]
  rfl
theorem sub2063 (p : Pattern) : d233 (change p 10000 none) = d233 p := by
  change (if p 133 then d232 (change p 10000 none) else d228 (change p 10000 none)) = d233 p
  rw [sub2062, sub2058]
  rfl
theorem sub2064 (p : Pattern) : d234 (change p 10000 none) = d234 p := by
  change (if p 133 then d66 (change p 10000 none) else d232 (change p 10000 none)) = d234 p
  rw [sub25, sub2062]
  rfl
theorem sub2065 (p : Pattern) : d235 (change p 10000 none) = d235 p := by
  change (if p 132 then d234 (change p 10000 none) else d233 (change p 10000 none)) = d235 p
  rw [sub2064, sub2063]
  rfl
theorem sub2066 (p : Pattern) : d236 (change p 10000 none) = d236 p := by
  change (if p 108 then d74 (change p 10000 none) else d235 (change p 10000 none)) = d236 p
  rw [sub33, sub2065]
  rfl
theorem sub2067 (p : Pattern) : d0 (change p 192 (some 193)) = d0 p := by
  rfl
theorem sub2068 (p : Pattern) : d24 (change p 192 (some 193)) = d0 p := by
  change d0 (change p 192 (some 193)) = d0 p
  exact sub2067 p
theorem sub2069 (p : Pattern) : d2 (change p 192 (some 193)) = d2 p := by
  rfl
theorem sub2070 (p : Pattern) : d525 (change p 192 (some 193)) = d2 p := by
  change d2 (change p 192 (some 193)) = d2 p
  exact sub2069 p
theorem sub2071 (p : Pattern) : d526 (change p 192 (some 193)) = d45 p := by
  change (if p 186 then d525 (change p 192 (some 193)) else d24 (change p 192 (some 193))) = d45 p
  rw [sub2070, sub2068]
  rfl
theorem sub2072 (p : Pattern) : d527 (change p 192 (some 193)) = d46 p := by
  change (if p 160 then d526 (change p 192 (some 193)) else d24 (change p 192 (some 193))) = d46 p
  rw [sub2071, sub2068]
  rfl
theorem sub2073 (p : Pattern) : d1 (change p 192 (some 193)) = d1 p := by
  rfl
theorem sub2074 (p : Pattern) : d8 (change p 192 (some 193)) = d8 p := by
  change (if p 271 then d1 (change p 192 (some 193)) else d0 (change p 192 (some 193))) = d8 p
  rw [sub2073, sub2067]
  rfl
theorem sub2075 (p : Pattern) : d25 (change p 192 (some 193)) = d8 p := by
  change d8 (change p 192 (some 193)) = d8 p
  exact sub2074 p
theorem sub2076 (p : Pattern) : d26 (change p 192 (some 193)) = d1055 p := by
  change (if p 168 then d25 (change p 192 (some 193)) else d24 (change p 192 (some 193))) = d1055 p
  rw [sub2075, sub2068]
  rfl
theorem sub2077 (p : Pattern) : d3 (change p 192 (some 193)) = d3 p := by
  rfl
theorem sub2078 (p : Pattern) : d9 (change p 192 (some 193)) = d9 p := by
  change (if p 271 then d3 (change p 192 (some 193)) else d2 (change p 192 (some 193))) = d9 p
  rw [sub2077, sub2069]
  rfl
theorem sub2079 (p : Pattern) : d528 (change p 192 (some 193)) = d9 p := by
  change d9 (change p 192 (some 193)) = d9 p
  exact sub2078 p
theorem sub2080 (p : Pattern) : d529 (change p 192 (some 193)) = d1056 p := by
  change (if p 186 then d528 (change p 192 (some 193)) else d25 (change p 192 (some 193))) = d1056 p
  rw [sub2079, sub2075]
  rfl
theorem sub2081 (p : Pattern) : d530 (change p 192 (some 193)) = d1057 p := by
  change (if p 168 then d529 (change p 192 (some 193)) else d526 (change p 192 (some 193))) = d1057 p
  rw [sub2080, sub2071]
  rfl
theorem sub2082 (p : Pattern) : d531 (change p 192 (some 193)) = d1058 p := by
  change (if p 160 then d530 (change p 192 (some 193)) else d26 (change p 192 (some 193))) = d1058 p
  rw [sub2081, sub2076]
  rfl
theorem sub2083 (p : Pattern) : d532 (change p 192 (some 193)) = d1059 p := by
  change (if p 141 then d531 (change p 192 (some 193)) else d527 (change p 192 (some 193))) = d1059 p
  rw [sub2082, sub2072]
  rfl
theorem sub2084 (p : Pattern) : d533 (change p 192 (some 193)) = d76 p := by
  change (if p 160 then d525 (change p 192 (some 193)) else d24 (change p 192 (some 193))) = d76 p
  rw [sub2070, sub2068]
  rfl
theorem sub2085 (p : Pattern) : d534 (change p 192 (some 193)) = d82 p := by
  change (if p 187 then d525 (change p 192 (some 193)) else d24 (change p 192 (some 193))) = d82 p
  rw [sub2070, sub2068]
  rfl
theorem sub2086 (p : Pattern) : d535 (change p 192 (some 193)) = d83 p := by
  change (if p 186 then d534 (change p 192 (some 193)) else d24 (change p 192 (some 193))) = d83 p
  rw [sub2085, sub2068]
  rfl
theorem sub2087 (p : Pattern) : d536 (change p 192 (some 193)) = d84 p := by
  change (if p 160 then d525 (change p 192 (some 193)) else d535 (change p 192 (some 193))) = d84 p
  rw [sub2070, sub2086]
  rfl
theorem sub2088 (p : Pattern) : d537 (change p 192 (some 193)) = d85 p := by
  change (if p 159 then d536 (change p 192 (some 193)) else d533 (change p 192 (some 193))) = d85 p
  rw [sub2087, sub2084]
  rfl
theorem sub2089 (p : Pattern) : d538 (change p 192 (some 193)) = d162 p := by
  change (if p 158 then d537 (change p 192 (some 193)) else d533 (change p 192 (some 193))) = d162 p
  rw [sub2088, sub2084]
  rfl
theorem sub2090 (p : Pattern) : d539 (change p 192 (some 193)) = d1060 p := by
  change (if p 168 then d528 (change p 192 (some 193)) else d525 (change p 192 (some 193))) = d1060 p
  rw [sub2079, sub2070]
  rfl
theorem sub2091 (p : Pattern) : d540 (change p 192 (some 193)) = d1061 p := by
  change (if p 160 then d539 (change p 192 (some 193)) else d26 (change p 192 (some 193))) = d1061 p
  rw [sub2090, sub2076]
  rfl
theorem sub2092 (p : Pattern) : d541 (change p 192 (some 193)) = d1062 p := by
  change (if p 187 then d528 (change p 192 (some 193)) else d25 (change p 192 (some 193))) = d1062 p
  rw [sub2079, sub2075]
  rfl
theorem sub2093 (p : Pattern) : d542 (change p 192 (some 193)) = d1063 p := by
  change (if p 186 then d541 (change p 192 (some 193)) else d25 (change p 192 (some 193))) = d1063 p
  rw [sub2092, sub2075]
  rfl
theorem sub2094 (p : Pattern) : d543 (change p 192 (some 193)) = d1064 p := by
  change (if p 168 then d542 (change p 192 (some 193)) else d535 (change p 192 (some 193))) = d1064 p
  rw [sub2093, sub2086]
  rfl
theorem sub2095 (p : Pattern) : d544 (change p 192 (some 193)) = d1065 p := by
  change (if p 160 then d539 (change p 192 (some 193)) else d543 (change p 192 (some 193))) = d1065 p
  rw [sub2090, sub2094]
  rfl
theorem sub2096 (p : Pattern) : d545 (change p 192 (some 193)) = d1066 p := by
  change (if p 159 then d544 (change p 192 (some 193)) else d540 (change p 192 (some 193))) = d1066 p
  rw [sub2095, sub2091]
  rfl
theorem sub2097 (p : Pattern) : d546 (change p 192 (some 193)) = d1067 p := by
  change (if p 158 then d545 (change p 192 (some 193)) else d540 (change p 192 (some 193))) = d1067 p
  rw [sub2096, sub2091]
  rfl
theorem sub2098 (p : Pattern) : d547 (change p 192 (some 193)) = d1068 p := by
  change (if p 141 then d546 (change p 192 (some 193)) else d538 (change p 192 (some 193))) = d1068 p
  rw [sub2097, sub2089]
  rfl
theorem sub2099 (p : Pattern) : d548 (change p 192 (some 193)) = d1069 p := by
  change (if p 134 then d547 (change p 192 (some 193)) else d532 (change p 192 (some 193))) = d1069 p
  rw [sub2098, sub2083]
  rfl
theorem sub2100 (p : Pattern) : d549 (change p 192 (some 193)) = d48 p := by
  change (if p 158 then d525 (change p 192 (some 193)) else d527 (change p 192 (some 193))) = d48 p
  rw [sub2070, sub2072]
  rfl
theorem sub2101 (p : Pattern) : d550 (change p 192 (some 193)) = d1070 p := by
  change (if p 158 then d539 (change p 192 (some 193)) else d531 (change p 192 (some 193))) = d1070 p
  rw [sub2090, sub2082]
  rfl
theorem sub2102 (p : Pattern) : d551 (change p 192 (some 193)) = d1071 p := by
  change (if p 141 then d550 (change p 192 (some 193)) else d549 (change p 192 (some 193))) = d1071 p
  rw [sub2101, sub2100]
  rfl
theorem sub2103 (p : Pattern) : d552 (change p 192 (some 193)) = d164 p := by
  change (if p 158 then d525 (change p 192 (some 193)) else d537 (change p 192 (some 193))) = d164 p
  rw [sub2070, sub2088]
  rfl
theorem sub2104 (p : Pattern) : d553 (change p 192 (some 193)) = d1072 p := by
  change (if p 158 then d539 (change p 192 (some 193)) else d545 (change p 192 (some 193))) = d1072 p
  rw [sub2090, sub2096]
  rfl
theorem sub2105 (p : Pattern) : d554 (change p 192 (some 193)) = d1073 p := by
  change (if p 141 then d553 (change p 192 (some 193)) else d552 (change p 192 (some 193))) = d1073 p
  rw [sub2104, sub2103]
  rfl
theorem sub2106 (p : Pattern) : d555 (change p 192 (some 193)) = d1074 p := by
  change (if p 134 then d554 (change p 192 (some 193)) else d551 (change p 192 (some 193))) = d1074 p
  rw [sub2105, sub2102]
  rfl
theorem sub2107 (p : Pattern) : d556 (change p 192 (some 193)) = d1075 p := by
  change (if p 133 then d555 (change p 192 (some 193)) else d548 (change p 192 (some 193))) = d1075 p
  rw [sub2106, sub2099]
  rfl
theorem sub2108 (p : Pattern) : d557 (change p 192 (some 193)) = d1076 p := by
  change (if p 141 then d539 (change p 192 (some 193)) else d525 (change p 192 (some 193))) = d1076 p
  rw [sub2090, sub2070]
  rfl
theorem sub2109 (p : Pattern) : d558 (change p 192 (some 193)) = d1077 p := by
  change (if p 133 then d557 (change p 192 (some 193)) else d555 (change p 192 (some 193))) = d1077 p
  rw [sub2108, sub2106]
  rfl
theorem sub2110 (p : Pattern) : d559 (change p 192 (some 193)) = d1078 p := by
  change (if p 132 then d558 (change p 192 (some 193)) else d556 (change p 192 (some 193))) = d1078 p
  rw [sub2109, sub2107]
  rfl
theorem sub2111 (p : Pattern) : d560 (change p 192 (some 193)) = d92 p := by
  change (if p 186 then d525 (change p 192 (some 193)) else d534 (change p 192 (some 193))) = d92 p
  rw [sub2070, sub2085]
  rfl
theorem sub2112 (p : Pattern) : d561 (change p 192 (some 193)) = d94 p := by
  change (if p 160 then d560 (change p 192 (some 193)) else d535 (change p 192 (some 193))) = d94 p
  rw [sub2111, sub2086]
  rfl
theorem sub2113 (p : Pattern) : d562 (change p 192 (some 193)) = d100 p := by
  change (if p 159 then d561 (change p 192 (some 193)) else d527 (change p 192 (some 193))) = d100 p
  rw [sub2112, sub2072]
  rfl
theorem sub2114 (p : Pattern) : d563 (change p 192 (some 193)) = d169 p := by
  change (if p 158 then d562 (change p 192 (some 193)) else d527 (change p 192 (some 193))) = d169 p
  rw [sub2113, sub2072]
  rfl
theorem sub2115 (p : Pattern) : d564 (change p 192 (some 193)) = d1079 p := by
  change (if p 186 then d528 (change p 192 (some 193)) else d541 (change p 192 (some 193))) = d1079 p
  rw [sub2079, sub2092]
  rfl
theorem sub2116 (p : Pattern) : d565 (change p 192 (some 193)) = d1080 p := by
  change (if p 168 then d564 (change p 192 (some 193)) else d560 (change p 192 (some 193))) = d1080 p
  rw [sub2115, sub2111]
  rfl
theorem sub2117 (p : Pattern) : d566 (change p 192 (some 193)) = d1081 p := by
  change (if p 160 then d565 (change p 192 (some 193)) else d543 (change p 192 (some 193))) = d1081 p
  rw [sub2116, sub2094]
  rfl
theorem sub2118 (p : Pattern) : d567 (change p 192 (some 193)) = d1082 p := by
  change (if p 159 then d566 (change p 192 (some 193)) else d531 (change p 192 (some 193))) = d1082 p
  rw [sub2117, sub2082]
  rfl
theorem sub2119 (p : Pattern) : d568 (change p 192 (some 193)) = d1083 p := by
  change (if p 158 then d567 (change p 192 (some 193)) else d531 (change p 192 (some 193))) = d1083 p
  rw [sub2118, sub2082]
  rfl
theorem sub2120 (p : Pattern) : d569 (change p 192 (some 193)) = d1084 p := by
  change (if p 141 then d568 (change p 192 (some 193)) else d563 (change p 192 (some 193))) = d1084 p
  rw [sub2119, sub2114]
  rfl
theorem sub2121 (p : Pattern) : d570 (change p 192 (some 193)) = d1085 p := by
  change (if p 134 then d557 (change p 192 (some 193)) else d569 (change p 192 (some 193))) = d1085 p
  rw [sub2108, sub2120]
  rfl
theorem sub2122 (p : Pattern) : d571 (change p 192 (some 193)) = d93 p := by
  change (if p 160 then d560 (change p 192 (some 193)) else d24 (change p 192 (some 193))) = d93 p
  rw [sub2111, sub2068]
  rfl
theorem sub2123 (p : Pattern) : d572 (change p 192 (some 193)) = d95 p := by
  change (if p 159 then d561 (change p 192 (some 193)) else d571 (change p 192 (some 193))) = d95 p
  rw [sub2112, sub2122]
  rfl
theorem sub2124 (p : Pattern) : d573 (change p 192 (some 193)) = d171 p := by
  change (if p 158 then d525 (change p 192 (some 193)) else d572 (change p 192 (some 193))) = d171 p
  rw [sub2070, sub2123]
  rfl
theorem sub2125 (p : Pattern) : d574 (change p 192 (some 193)) = d1086 p := by
  change (if p 160 then d565 (change p 192 (some 193)) else d26 (change p 192 (some 193))) = d1086 p
  rw [sub2116, sub2076]
  rfl
theorem sub2126 (p : Pattern) : d575 (change p 192 (some 193)) = d1087 p := by
  change (if p 159 then d566 (change p 192 (some 193)) else d574 (change p 192 (some 193))) = d1087 p
  rw [sub2117, sub2125]
  rfl
theorem sub2127 (p : Pattern) : d576 (change p 192 (some 193)) = d1088 p := by
  change (if p 158 then d539 (change p 192 (some 193)) else d575 (change p 192 (some 193))) = d1088 p
  rw [sub2090, sub2126]
  rfl
theorem sub2128 (p : Pattern) : d577 (change p 192 (some 193)) = d1089 p := by
  change (if p 141 then d576 (change p 192 (some 193)) else d573 (change p 192 (some 193))) = d1089 p
  rw [sub2127, sub2124]
  rfl
theorem sub2129 (p : Pattern) : d578 (change p 192 (some 193)) = d1090 p := by
  change (if p 134 then d557 (change p 192 (some 193)) else d577 (change p 192 (some 193))) = d1090 p
  rw [sub2108, sub2128]
  rfl
theorem sub2130 (p : Pattern) : d579 (change p 192 (some 193)) = d1091 p := by
  change (if p 133 then d578 (change p 192 (some 193)) else d570 (change p 192 (some 193))) = d1091 p
  rw [sub2129, sub2121]
  rfl
theorem sub2131 (p : Pattern) : d580 (change p 192 (some 193)) = d174 p := by
  change (if p 158 then d525 (change p 192 (some 193)) else d562 (change p 192 (some 193))) = d174 p
  rw [sub2070, sub2113]
  rfl
theorem sub2132 (p : Pattern) : d581 (change p 192 (some 193)) = d1092 p := by
  change (if p 158 then d539 (change p 192 (some 193)) else d567 (change p 192 (some 193))) = d1092 p
  rw [sub2090, sub2118]
  rfl
theorem sub2133 (p : Pattern) : d582 (change p 192 (some 193)) = d1093 p := by
  change (if p 141 then d581 (change p 192 (some 193)) else d580 (change p 192 (some 193))) = d1093 p
  rw [sub2132, sub2131]
  rfl
theorem sub2134 (p : Pattern) : d583 (change p 192 (some 193)) = d1094 p := by
  change (if p 134 then d557 (change p 192 (some 193)) else d582 (change p 192 (some 193))) = d1094 p
  rw [sub2108, sub2133]
  rfl
theorem sub2135 (p : Pattern) : d584 (change p 192 (some 193)) = d1095 p := by
  change (if p 133 then d557 (change p 192 (some 193)) else d583 (change p 192 (some 193))) = d1095 p
  rw [sub2108, sub2134]
  rfl
theorem sub2136 (p : Pattern) : d585 (change p 192 (some 193)) = d1096 p := by
  change (if p 132 then d584 (change p 192 (some 193)) else d579 (change p 192 (some 193))) = d1096 p
  rw [sub2135, sub2130]
  rfl
theorem sub2137 (p : Pattern) : d586 (change p 192 (some 193)) = d1097 p := by
  change (if p 108 then d585 (change p 192 (some 193)) else d559 (change p 192 (some 193))) = d1097 p
  rw [sub2136, sub2110]
  rfl
theorem sub2138 (p : Pattern) : d1 (change p 10000 (some 141)) = d1 p := by
  rfl
theorem sub2139 (p : Pattern) : d8 (change p 10000 (some 141)) = d8 p := by
  change (if p 271 then d1 (change p 10000 (some 141)) else d0 (change p 10000 (some 141))) = d8 p
  rw [sub2138, sub1092]
  rfl
theorem sub2140 (p : Pattern) : d3 (change p 10000 (some 141)) = d3 p := by
  rfl
theorem sub2141 (p : Pattern) : d9 (change p 10000 (some 141)) = d9 p := by
  change (if p 271 then d3 (change p 10000 (some 141)) else d2 (change p 10000 (some 141))) = d9 p
  rw [sub2140, sub1093]
  rfl
theorem sub2142 (p : Pattern) : d10 (change p 10000 (some 141)) = d10 p := by
  change (if p 193 then d9 (change p 10000 (some 141)) else d8 (change p 10000 (some 141))) = d10 p
  rw [sub2141, sub2139]
  rfl
theorem sub2143 (p : Pattern) : d11 (change p 10000 (some 141)) = d11 p := by
  change (if p 192 then d10 (change p 10000 (some 141)) else d8 (change p 10000 (some 141))) = d11 p
  rw [sub2142, sub2139]
  rfl
theorem sub2144 (p : Pattern) : d12 (change p 10000 (some 141)) = d12 p := by
  change (if p 168 then d11 (change p 10000 (some 141)) else d7 (change p 10000 (some 141))) = d12 p
  rw [sub2143, sub1095]
  rfl
theorem sub2145 (p : Pattern) : d5 (change p 10000 (some 141)) = d5 p := by
  rfl
theorem sub2146 (p : Pattern) : d58 (change p 10000 (some 141)) = d58 p := by
  change (if p 271 then d5 (change p 10000 (some 141)) else d4 (change p 10000 (some 141))) = d58 p
  rw [sub2145, sub1096]
  rfl
theorem sub2147 (p : Pattern) : d59 (change p 10000 (some 141)) = d59 p := by
  change (if p 193 then d58 (change p 10000 (some 141)) else d9 (change p 10000 (some 141))) = d59 p
  rw [sub2146, sub2141]
  rfl
theorem sub2148 (p : Pattern) : d60 (change p 10000 (some 141)) = d60 p := by
  change (if p 192 then d59 (change p 10000 (some 141)) else d9 (change p 10000 (some 141))) = d60 p
  rw [sub2147, sub2141]
  rfl
theorem sub2149 (p : Pattern) : d61 (change p 10000 (some 141)) = d61 p := by
  change (if p 186 then d60 (change p 10000 (some 141)) else d11 (change p 10000 (some 141))) = d61 p
  rw [sub2148, sub2143]
  rfl
theorem sub2150 (p : Pattern) : d62 (change p 10000 (some 141)) = d62 p := by
  change (if p 168 then d61 (change p 10000 (some 141)) else d56 (change p 10000 (some 141))) = d62 p
  rw [sub2149, sub1099]
  rfl
theorem sub2151 (p : Pattern) : d63 (change p 10000 (some 141)) = d63 p := by
  change (if p 160 then d62 (change p 10000 (some 141)) else d12 (change p 10000 (some 141))) = d63 p
  rw [sub2150, sub2144]
  rfl
theorem sub2152 (p : Pattern) : d64 (change p 10000 (some 141)) = d63 p := by
  change d63 (change p 10000 (some 141)) = d63 p
  exact sub2151 p
theorem sub2153 (p : Pattern) : d65 (change p 10000 (some 141)) = d65 p := by
  change (if p 168 then d60 (change p 10000 (some 141)) else d55 (change p 10000 (some 141))) = d65 p
  rw [sub2148, sub1098]
  rfl
theorem sub2154 (p : Pattern) : d109 (change p 10000 (some 141)) = d109 p := by
  change (if p 160 then d65 (change p 10000 (some 141)) else d12 (change p 10000 (some 141))) = d109 p
  rw [sub2153, sub2144]
  rfl
theorem sub2155 (p : Pattern) : d125 (change p 10000 (some 141)) = d125 p := by
  change (if p 187 then d60 (change p 10000 (some 141)) else d11 (change p 10000 (some 141))) = d125 p
  rw [sub2148, sub2143]
  rfl
theorem sub2156 (p : Pattern) : d126 (change p 10000 (some 141)) = d126 p := by
  change (if p 186 then d125 (change p 10000 (some 141)) else d11 (change p 10000 (some 141))) = d126 p
  rw [sub2155, sub2143]
  rfl
theorem sub2157 (p : Pattern) : d127 (change p 10000 (some 141)) = d127 p := by
  change (if p 168 then d126 (change p 10000 (some 141)) else d120 (change p 10000 (some 141))) = d127 p
  rw [sub2156, sub1103]
  rfl
theorem sub2158 (p : Pattern) : d128 (change p 10000 (some 141)) = d128 p := by
  change (if p 160 then d65 (change p 10000 (some 141)) else d127 (change p 10000 (some 141))) = d128 p
  rw [sub2153, sub2157]
  rfl
theorem sub2159 (p : Pattern) : d129 (change p 10000 (some 141)) = d129 p := by
  change (if p 159 then d128 (change p 10000 (some 141)) else d109 (change p 10000 (some 141))) = d129 p
  rw [sub2158, sub2154]
  rfl
end NetHack.Sokoban12CostPartition
