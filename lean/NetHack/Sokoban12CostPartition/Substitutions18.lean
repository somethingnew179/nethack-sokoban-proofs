/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions17
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2160 (p : Pattern) : d237 (change p 10000 (some 141)) = d237 p := by
  change (if p 158 then d129 (change p 10000 (some 141)) else d109 (change p 10000 (some 141))) = d237 p
  rw [sub2159, sub2154]
  rfl
theorem sub2161 (p : Pattern) : d238 (change p 10000 (some 141)) = d237 p := by
  change d237 (change p 10000 (some 141)) = d237 p
  exact sub2160 p
theorem sub2162 (p : Pattern) : d239 (change p 10000 (some 141)) = d1177 p := by
  change (if p 134 then d238 (change p 10000 (some 141)) else d64 (change p 10000 (some 141))) = d1177 p
  rw [sub2161, sub2152]
  rfl
theorem sub2163 (p : Pattern) : d69 (change p 10000 (some 141)) = d69 p := by
  change (if p 158 then d65 (change p 10000 (some 141)) else d63 (change p 10000 (some 141))) = d69 p
  rw [sub2153, sub2151]
  rfl
theorem sub2164 (p : Pattern) : d70 (change p 10000 (some 141)) = d69 p := by
  change d69 (change p 10000 (some 141)) = d69 p
  exact sub2163 p
theorem sub2165 (p : Pattern) : d240 (change p 10000 (some 141)) = d240 p := by
  change (if p 158 then d65 (change p 10000 (some 141)) else d129 (change p 10000 (some 141))) = d240 p
  rw [sub2153, sub2159]
  rfl
theorem sub2166 (p : Pattern) : d241 (change p 10000 (some 141)) = d240 p := by
  change d240 (change p 10000 (some 141)) = d240 p
  exact sub2165 p
theorem sub2167 (p : Pattern) : d242 (change p 10000 (some 141)) = d1178 p := by
  change (if p 134 then d241 (change p 10000 (some 141)) else d70 (change p 10000 (some 141))) = d1178 p
  rw [sub2166, sub2164]
  rfl
theorem sub2168 (p : Pattern) : d243 (change p 10000 (some 141)) = d1179 p := by
  change (if p 133 then d242 (change p 10000 (some 141)) else d239 (change p 10000 (some 141))) = d1179 p
  rw [sub2167, sub2162]
  rfl
theorem sub2169 (p : Pattern) : d66 (change p 10000 (some 141)) = d65 p := by
  change d65 (change p 10000 (some 141)) = d65 p
  exact sub2153 p
theorem sub2170 (p : Pattern) : d244 (change p 10000 (some 141)) = d1180 p := by
  change (if p 133 then d66 (change p 10000 (some 141)) else d242 (change p 10000 (some 141))) = d1180 p
  rw [sub2169, sub2167]
  rfl
theorem sub2171 (p : Pattern) : d245 (change p 10000 (some 141)) = d1181 p := by
  change (if p 132 then d244 (change p 10000 (some 141)) else d243 (change p 10000 (some 141))) = d1181 p
  rw [sub2170, sub2168]
  rfl
theorem sub2172 (p : Pattern) : d143 (change p 10000 (some 141)) = d143 p := by
  change (if p 186 then d60 (change p 10000 (some 141)) else d125 (change p 10000 (some 141))) = d143 p
  rw [sub2148, sub2155]
  rfl
theorem sub2173 (p : Pattern) : d144 (change p 10000 (some 141)) = d144 p := by
  change (if p 168 then d143 (change p 10000 (some 141)) else d137 (change p 10000 (some 141))) = d144 p
  rw [sub2172, sub1114]
  rfl
theorem sub2174 (p : Pattern) : d146 (change p 10000 (some 141)) = d146 p := by
  change (if p 160 then d144 (change p 10000 (some 141)) else d127 (change p 10000 (some 141))) = d146 p
  rw [sub2173, sub2157]
  rfl
theorem sub2175 (p : Pattern) : d155 (change p 10000 (some 141)) = d155 p := by
  change (if p 159 then d146 (change p 10000 (some 141)) else d63 (change p 10000 (some 141))) = d155 p
  rw [sub2174, sub2151]
  rfl
theorem sub2176 (p : Pattern) : d246 (change p 10000 (some 141)) = d246 p := by
  change (if p 158 then d155 (change p 10000 (some 141)) else d63 (change p 10000 (some 141))) = d246 p
  rw [sub2175, sub2151]
  rfl
theorem sub2177 (p : Pattern) : d247 (change p 10000 (some 141)) = d246 p := by
  change d246 (change p 10000 (some 141)) = d246 p
  exact sub2176 p
theorem sub2178 (p : Pattern) : d248 (change p 10000 (some 141)) = d1182 p := by
  change (if p 134 then d66 (change p 10000 (some 141)) else d247 (change p 10000 (some 141))) = d1182 p
  rw [sub2169, sub2177]
  rfl
theorem sub2179 (p : Pattern) : d145 (change p 10000 (some 141)) = d145 p := by
  change (if p 160 then d144 (change p 10000 (some 141)) else d12 (change p 10000 (some 141))) = d145 p
  rw [sub2173, sub2144]
  rfl
theorem sub2180 (p : Pattern) : d147 (change p 10000 (some 141)) = d147 p := by
  change (if p 159 then d146 (change p 10000 (some 141)) else d145 (change p 10000 (some 141))) = d147 p
  rw [sub2174, sub2179]
  rfl
theorem sub2181 (p : Pattern) : d249 (change p 10000 (some 141)) = d249 p := by
  change (if p 158 then d65 (change p 10000 (some 141)) else d147 (change p 10000 (some 141))) = d249 p
  rw [sub2153, sub2180]
  rfl
theorem sub2182 (p : Pattern) : d250 (change p 10000 (some 141)) = d249 p := by
  change d249 (change p 10000 (some 141)) = d249 p
  exact sub2181 p
theorem sub2183 (p : Pattern) : d251 (change p 10000 (some 141)) = d1183 p := by
  change (if p 134 then d66 (change p 10000 (some 141)) else d250 (change p 10000 (some 141))) = d1183 p
  rw [sub2169, sub2182]
  rfl
theorem sub2184 (p : Pattern) : d252 (change p 10000 (some 141)) = d1184 p := by
  change (if p 133 then d251 (change p 10000 (some 141)) else d248 (change p 10000 (some 141))) = d1184 p
  rw [sub2183, sub2178]
  rfl
theorem sub2185 (p : Pattern) : d253 (change p 10000 (some 141)) = d253 p := by
  change (if p 158 then d65 (change p 10000 (some 141)) else d155 (change p 10000 (some 141))) = d253 p
  rw [sub2153, sub2175]
  rfl
theorem sub2186 (p : Pattern) : d254 (change p 10000 (some 141)) = d253 p := by
  change d253 (change p 10000 (some 141)) = d253 p
  exact sub2185 p
theorem sub2187 (p : Pattern) : d255 (change p 10000 (some 141)) = d1185 p := by
  change (if p 134 then d66 (change p 10000 (some 141)) else d254 (change p 10000 (some 141))) = d1185 p
  rw [sub2169, sub2186]
  rfl
theorem sub2188 (p : Pattern) : d256 (change p 10000 (some 141)) = d1186 p := by
  change (if p 133 then d66 (change p 10000 (some 141)) else d255 (change p 10000 (some 141))) = d1186 p
  rw [sub2169, sub2187]
  rfl
theorem sub2189 (p : Pattern) : d257 (change p 10000 (some 141)) = d1187 p := by
  change (if p 132 then d256 (change p 10000 (some 141)) else d252 (change p 10000 (some 141))) = d1187 p
  rw [sub2188, sub2184]
  rfl
theorem sub2190 (p : Pattern) : d258 (change p 10000 (some 141)) = d1188 p := by
  change (if p 108 then d257 (change p 10000 (some 141)) else d245 (change p 10000 (some 141))) = d1188 p
  rw [sub2189, sub2171]
  rfl
theorem sub2191 (p : Pattern) : d0 (change p 193 (some 192)) = d0 p := by
  rfl
theorem sub2192 (p : Pattern) : d28 (change p 193 (some 192)) = d0 p := by
  change d0 (change p 193 (some 192)) = d0 p
  exact sub2191 p
theorem sub2193 (p : Pattern) : d29 (change p 193 (some 192)) = d0 p := by
  change d28 (change p 193 (some 192)) = d0 p
  exact sub2192 p
theorem sub2194 (p : Pattern) : d30 (change p 193 (some 192)) = d0 p := by
  change d28 (change p 193 (some 192)) = d0 p
  exact sub2192 p
theorem sub2195 (p : Pattern) : d31 (change p 193 (some 192)) = d0 p := by
  change (if p 168 then d30 (change p 193 (some 192)) else d29 (change p 193 (some 192))) = d0 p
  rw [sub2194, sub2193]
  simp only [ite_self]
theorem sub2196 (p : Pattern) : d2 (change p 193 (some 192)) = d2 p := by
  rfl
theorem sub2197 (p : Pattern) : d587 (change p 193 (some 192)) = d2 p := by
  change d2 (change p 193 (some 192)) = d2 p
  exact sub2196 p
theorem sub2198 (p : Pattern) : d588 (change p 193 (some 192)) = d2 p := by
  change d587 (change p 193 (some 192)) = d2 p
  exact sub2197 p
theorem sub2199 (p : Pattern) : d589 (change p 193 (some 192)) = d45 p := by
  change (if p 186 then d588 (change p 193 (some 192)) else d29 (change p 193 (some 192))) = d45 p
  rw [sub2198, sub2193]
  rfl
theorem sub2200 (p : Pattern) : d590 (change p 193 (some 192)) = d2 p := by
  change d587 (change p 193 (some 192)) = d2 p
  exact sub2197 p
theorem sub2201 (p : Pattern) : d591 (change p 193 (some 192)) = d45 p := by
  change (if p 186 then d590 (change p 193 (some 192)) else d30 (change p 193 (some 192))) = d45 p
  rw [sub2200, sub2194]
  rfl
theorem sub2202 (p : Pattern) : d592 (change p 193 (some 192)) = d45 p := by
  change (if p 168 then d591 (change p 193 (some 192)) else d589 (change p 193 (some 192))) = d45 p
  rw [sub2201, sub2199]
  simp only [ite_self]
theorem sub2203 (p : Pattern) : d593 (change p 193 (some 192)) = d46 p := by
  change (if p 160 then d592 (change p 193 (some 192)) else d31 (change p 193 (some 192))) = d46 p
  rw [sub2202, sub2195]
  rfl
theorem sub2204 (p : Pattern) : d1 (change p 193 (some 192)) = d1 p := by
  rfl
theorem sub2205 (p : Pattern) : d8 (change p 193 (some 192)) = d8 p := by
  change (if p 271 then d1 (change p 193 (some 192)) else d0 (change p 193 (some 192))) = d8 p
  rw [sub2204, sub2191]
  rfl
theorem sub2206 (p : Pattern) : d32 (change p 193 (some 192)) = d8 p := by
  change d8 (change p 193 (some 192)) = d8 p
  exact sub2205 p
theorem sub2207 (p : Pattern) : d33 (change p 193 (some 192)) = d1055 p := by
  change (if p 168 then d32 (change p 193 (some 192)) else d30 (change p 193 (some 192))) = d1055 p
  rw [sub2206, sub2194]
  rfl
theorem sub2208 (p : Pattern) : d3 (change p 193 (some 192)) = d3 p := by
  rfl
theorem sub2209 (p : Pattern) : d9 (change p 193 (some 192)) = d9 p := by
  change (if p 271 then d3 (change p 193 (some 192)) else d2 (change p 193 (some 192))) = d9 p
  rw [sub2208, sub2196]
  rfl
theorem sub2210 (p : Pattern) : d594 (change p 193 (some 192)) = d9 p := by
  change d9 (change p 193 (some 192)) = d9 p
  exact sub2209 p
theorem sub2211 (p : Pattern) : d595 (change p 193 (some 192)) = d1056 p := by
  change (if p 186 then d594 (change p 193 (some 192)) else d32 (change p 193 (some 192))) = d1056 p
  rw [sub2210, sub2206]
  rfl
theorem sub2212 (p : Pattern) : d596 (change p 193 (some 192)) = d1057 p := by
  change (if p 168 then d595 (change p 193 (some 192)) else d591 (change p 193 (some 192))) = d1057 p
  rw [sub2211, sub2201]
  rfl
theorem sub2213 (p : Pattern) : d597 (change p 193 (some 192)) = d1058 p := by
  change (if p 160 then d596 (change p 193 (some 192)) else d33 (change p 193 (some 192))) = d1058 p
  rw [sub2212, sub2207]
  rfl
theorem sub2214 (p : Pattern) : d598 (change p 193 (some 192)) = d1059 p := by
  change (if p 141 then d597 (change p 193 (some 192)) else d593 (change p 193 (some 192))) = d1059 p
  rw [sub2213, sub2203]
  rfl
theorem sub2215 (p : Pattern) : d599 (change p 193 (some 192)) = d2 p := by
  change (if p 168 then d590 (change p 193 (some 192)) else d588 (change p 193 (some 192))) = d2 p
  rw [sub2200, sub2198]
  simp only [ite_self]
theorem sub2216 (p : Pattern) : d600 (change p 193 (some 192)) = d76 p := by
  change (if p 160 then d599 (change p 193 (some 192)) else d31 (change p 193 (some 192))) = d76 p
  rw [sub2215, sub2195]
  rfl
theorem sub2217 (p : Pattern) : d601 (change p 193 (some 192)) = d82 p := by
  change (if p 187 then d588 (change p 193 (some 192)) else d29 (change p 193 (some 192))) = d82 p
  rw [sub2198, sub2193]
  rfl
theorem sub2218 (p : Pattern) : d602 (change p 193 (some 192)) = d83 p := by
  change (if p 186 then d601 (change p 193 (some 192)) else d29 (change p 193 (some 192))) = d83 p
  rw [sub2217, sub2193]
  rfl
theorem sub2219 (p : Pattern) : d603 (change p 193 (some 192)) = d82 p := by
  change (if p 187 then d590 (change p 193 (some 192)) else d30 (change p 193 (some 192))) = d82 p
  rw [sub2200, sub2194]
  rfl
theorem sub2220 (p : Pattern) : d604 (change p 193 (some 192)) = d83 p := by
  change (if p 186 then d603 (change p 193 (some 192)) else d30 (change p 193 (some 192))) = d83 p
  rw [sub2219, sub2194]
  rfl
theorem sub2221 (p : Pattern) : d605 (change p 193 (some 192)) = d83 p := by
  change (if p 168 then d604 (change p 193 (some 192)) else d602 (change p 193 (some 192))) = d83 p
  rw [sub2220, sub2218]
  simp only [ite_self]
theorem sub2222 (p : Pattern) : d606 (change p 193 (some 192)) = d84 p := by
  change (if p 160 then d599 (change p 193 (some 192)) else d605 (change p 193 (some 192))) = d84 p
  rw [sub2215, sub2221]
  rfl
theorem sub2223 (p : Pattern) : d607 (change p 193 (some 192)) = d85 p := by
  change (if p 159 then d606 (change p 193 (some 192)) else d600 (change p 193 (some 192))) = d85 p
  rw [sub2222, sub2216]
  rfl
theorem sub2224 (p : Pattern) : d608 (change p 193 (some 192)) = d162 p := by
  change (if p 158 then d607 (change p 193 (some 192)) else d600 (change p 193 (some 192))) = d162 p
  rw [sub2223, sub2216]
  rfl
theorem sub2225 (p : Pattern) : d609 (change p 193 (some 192)) = d1060 p := by
  change (if p 168 then d594 (change p 193 (some 192)) else d590 (change p 193 (some 192))) = d1060 p
  rw [sub2210, sub2200]
  rfl
theorem sub2226 (p : Pattern) : d610 (change p 193 (some 192)) = d1061 p := by
  change (if p 160 then d609 (change p 193 (some 192)) else d33 (change p 193 (some 192))) = d1061 p
  rw [sub2225, sub2207]
  rfl
theorem sub2227 (p : Pattern) : d611 (change p 193 (some 192)) = d1062 p := by
  change (if p 187 then d594 (change p 193 (some 192)) else d32 (change p 193 (some 192))) = d1062 p
  rw [sub2210, sub2206]
  rfl
theorem sub2228 (p : Pattern) : d612 (change p 193 (some 192)) = d1063 p := by
  change (if p 186 then d611 (change p 193 (some 192)) else d32 (change p 193 (some 192))) = d1063 p
  rw [sub2227, sub2206]
  rfl
theorem sub2229 (p : Pattern) : d613 (change p 193 (some 192)) = d1064 p := by
  change (if p 168 then d612 (change p 193 (some 192)) else d604 (change p 193 (some 192))) = d1064 p
  rw [sub2228, sub2220]
  rfl
theorem sub2230 (p : Pattern) : d614 (change p 193 (some 192)) = d1065 p := by
  change (if p 160 then d609 (change p 193 (some 192)) else d613 (change p 193 (some 192))) = d1065 p
  rw [sub2225, sub2229]
  rfl
theorem sub2231 (p : Pattern) : d615 (change p 193 (some 192)) = d1066 p := by
  change (if p 159 then d614 (change p 193 (some 192)) else d610 (change p 193 (some 192))) = d1066 p
  rw [sub2230, sub2226]
  rfl
theorem sub2232 (p : Pattern) : d616 (change p 193 (some 192)) = d1067 p := by
  change (if p 158 then d615 (change p 193 (some 192)) else d610 (change p 193 (some 192))) = d1067 p
  rw [sub2231, sub2226]
  rfl
theorem sub2233 (p : Pattern) : d617 (change p 193 (some 192)) = d1068 p := by
  change (if p 141 then d616 (change p 193 (some 192)) else d608 (change p 193 (some 192))) = d1068 p
  rw [sub2232, sub2224]
  rfl
theorem sub2234 (p : Pattern) : d618 (change p 193 (some 192)) = d1069 p := by
  change (if p 134 then d617 (change p 193 (some 192)) else d598 (change p 193 (some 192))) = d1069 p
  rw [sub2233, sub2214]
  rfl
theorem sub2235 (p : Pattern) : d619 (change p 193 (some 192)) = d48 p := by
  change (if p 158 then d599 (change p 193 (some 192)) else d593 (change p 193 (some 192))) = d48 p
  rw [sub2215, sub2203]
  rfl
theorem sub2236 (p : Pattern) : d620 (change p 193 (some 192)) = d1070 p := by
  change (if p 158 then d609 (change p 193 (some 192)) else d597 (change p 193 (some 192))) = d1070 p
  rw [sub2225, sub2213]
  rfl
theorem sub2237 (p : Pattern) : d621 (change p 193 (some 192)) = d1071 p := by
  change (if p 141 then d620 (change p 193 (some 192)) else d619 (change p 193 (some 192))) = d1071 p
  rw [sub2236, sub2235]
  rfl
theorem sub2238 (p : Pattern) : d622 (change p 193 (some 192)) = d164 p := by
  change (if p 158 then d599 (change p 193 (some 192)) else d607 (change p 193 (some 192))) = d164 p
  rw [sub2215, sub2223]
  rfl
theorem sub2239 (p : Pattern) : d623 (change p 193 (some 192)) = d1072 p := by
  change (if p 158 then d609 (change p 193 (some 192)) else d615 (change p 193 (some 192))) = d1072 p
  rw [sub2225, sub2231]
  rfl
theorem sub2240 (p : Pattern) : d624 (change p 193 (some 192)) = d1073 p := by
  change (if p 141 then d623 (change p 193 (some 192)) else d622 (change p 193 (some 192))) = d1073 p
  rw [sub2239, sub2238]
  rfl
theorem sub2241 (p : Pattern) : d625 (change p 193 (some 192)) = d1074 p := by
  change (if p 134 then d624 (change p 193 (some 192)) else d621 (change p 193 (some 192))) = d1074 p
  rw [sub2240, sub2237]
  rfl
theorem sub2242 (p : Pattern) : d626 (change p 193 (some 192)) = d1075 p := by
  change (if p 133 then d625 (change p 193 (some 192)) else d618 (change p 193 (some 192))) = d1075 p
  rw [sub2241, sub2234]
  rfl
theorem sub2243 (p : Pattern) : d627 (change p 193 (some 192)) = d1076 p := by
  change (if p 141 then d609 (change p 193 (some 192)) else d599 (change p 193 (some 192))) = d1076 p
  rw [sub2225, sub2215]
  rfl
theorem sub2244 (p : Pattern) : d628 (change p 193 (some 192)) = d1077 p := by
  change (if p 133 then d627 (change p 193 (some 192)) else d625 (change p 193 (some 192))) = d1077 p
  rw [sub2243, sub2241]
  rfl
theorem sub2245 (p : Pattern) : d629 (change p 193 (some 192)) = d1078 p := by
  change (if p 132 then d628 (change p 193 (some 192)) else d626 (change p 193 (some 192))) = d1078 p
  rw [sub2244, sub2242]
  rfl
theorem sub2246 (p : Pattern) : d630 (change p 193 (some 192)) = d92 p := by
  change (if p 186 then d588 (change p 193 (some 192)) else d601 (change p 193 (some 192))) = d92 p
  rw [sub2198, sub2217]
  rfl
theorem sub2247 (p : Pattern) : d631 (change p 193 (some 192)) = d92 p := by
  change (if p 186 then d590 (change p 193 (some 192)) else d603 (change p 193 (some 192))) = d92 p
  rw [sub2200, sub2219]
  rfl
theorem sub2248 (p : Pattern) : d632 (change p 193 (some 192)) = d92 p := by
  change (if p 168 then d631 (change p 193 (some 192)) else d630 (change p 193 (some 192))) = d92 p
  rw [sub2247, sub2246]
  simp only [ite_self]
theorem sub2249 (p : Pattern) : d633 (change p 193 (some 192)) = d94 p := by
  change (if p 160 then d632 (change p 193 (some 192)) else d605 (change p 193 (some 192))) = d94 p
  rw [sub2248, sub2221]
  rfl
theorem sub2250 (p : Pattern) : d634 (change p 193 (some 192)) = d100 p := by
  change (if p 159 then d633 (change p 193 (some 192)) else d593 (change p 193 (some 192))) = d100 p
  rw [sub2249, sub2203]
  rfl
theorem sub2251 (p : Pattern) : d635 (change p 193 (some 192)) = d169 p := by
  change (if p 158 then d634 (change p 193 (some 192)) else d593 (change p 193 (some 192))) = d169 p
  rw [sub2250, sub2203]
  rfl
theorem sub2252 (p : Pattern) : d636 (change p 193 (some 192)) = d1079 p := by
  change (if p 186 then d594 (change p 193 (some 192)) else d611 (change p 193 (some 192))) = d1079 p
  rw [sub2210, sub2227]
  rfl
theorem sub2253 (p : Pattern) : d637 (change p 193 (some 192)) = d1080 p := by
  change (if p 168 then d636 (change p 193 (some 192)) else d631 (change p 193 (some 192))) = d1080 p
  rw [sub2252, sub2247]
  rfl
theorem sub2254 (p : Pattern) : d638 (change p 193 (some 192)) = d1081 p := by
  change (if p 160 then d637 (change p 193 (some 192)) else d613 (change p 193 (some 192))) = d1081 p
  rw [sub2253, sub2229]
  rfl
theorem sub2255 (p : Pattern) : d639 (change p 193 (some 192)) = d1082 p := by
  change (if p 159 then d638 (change p 193 (some 192)) else d597 (change p 193 (some 192))) = d1082 p
  rw [sub2254, sub2213]
  rfl
theorem sub2256 (p : Pattern) : d640 (change p 193 (some 192)) = d1083 p := by
  change (if p 158 then d639 (change p 193 (some 192)) else d597 (change p 193 (some 192))) = d1083 p
  rw [sub2255, sub2213]
  rfl
theorem sub2257 (p : Pattern) : d641 (change p 193 (some 192)) = d1084 p := by
  change (if p 141 then d640 (change p 193 (some 192)) else d635 (change p 193 (some 192))) = d1084 p
  rw [sub2256, sub2251]
  rfl
theorem sub2258 (p : Pattern) : d642 (change p 193 (some 192)) = d1085 p := by
  change (if p 134 then d627 (change p 193 (some 192)) else d641 (change p 193 (some 192))) = d1085 p
  rw [sub2243, sub2257]
  rfl
theorem sub2259 (p : Pattern) : d643 (change p 193 (some 192)) = d93 p := by
  change (if p 160 then d632 (change p 193 (some 192)) else d31 (change p 193 (some 192))) = d93 p
  rw [sub2248, sub2195]
  rfl
theorem sub2260 (p : Pattern) : d644 (change p 193 (some 192)) = d95 p := by
  change (if p 159 then d633 (change p 193 (some 192)) else d643 (change p 193 (some 192))) = d95 p
  rw [sub2249, sub2259]
  rfl
theorem sub2261 (p : Pattern) : d645 (change p 193 (some 192)) = d171 p := by
  change (if p 158 then d599 (change p 193 (some 192)) else d644 (change p 193 (some 192))) = d171 p
  rw [sub2215, sub2260]
  rfl
theorem sub2262 (p : Pattern) : d646 (change p 193 (some 192)) = d1086 p := by
  change (if p 160 then d637 (change p 193 (some 192)) else d33 (change p 193 (some 192))) = d1086 p
  rw [sub2253, sub2207]
  rfl
theorem sub2263 (p : Pattern) : d647 (change p 193 (some 192)) = d1087 p := by
  change (if p 159 then d638 (change p 193 (some 192)) else d646 (change p 193 (some 192))) = d1087 p
  rw [sub2254, sub2262]
  rfl
theorem sub2264 (p : Pattern) : d648 (change p 193 (some 192)) = d1088 p := by
  change (if p 158 then d609 (change p 193 (some 192)) else d647 (change p 193 (some 192))) = d1088 p
  rw [sub2225, sub2263]
  rfl
theorem sub2265 (p : Pattern) : d649 (change p 193 (some 192)) = d1089 p := by
  change (if p 141 then d648 (change p 193 (some 192)) else d645 (change p 193 (some 192))) = d1089 p
  rw [sub2264, sub2261]
  rfl
theorem sub2266 (p : Pattern) : d650 (change p 193 (some 192)) = d1090 p := by
  change (if p 134 then d627 (change p 193 (some 192)) else d649 (change p 193 (some 192))) = d1090 p
  rw [sub2243, sub2265]
  rfl
theorem sub2267 (p : Pattern) : d651 (change p 193 (some 192)) = d1091 p := by
  change (if p 133 then d650 (change p 193 (some 192)) else d642 (change p 193 (some 192))) = d1091 p
  rw [sub2266, sub2258]
  rfl
theorem sub2268 (p : Pattern) : d652 (change p 193 (some 192)) = d174 p := by
  change (if p 158 then d599 (change p 193 (some 192)) else d634 (change p 193 (some 192))) = d174 p
  rw [sub2215, sub2250]
  rfl
theorem sub2269 (p : Pattern) : d653 (change p 193 (some 192)) = d1092 p := by
  change (if p 158 then d609 (change p 193 (some 192)) else d639 (change p 193 (some 192))) = d1092 p
  rw [sub2225, sub2255]
  rfl
theorem sub2270 (p : Pattern) : d654 (change p 193 (some 192)) = d1093 p := by
  change (if p 141 then d653 (change p 193 (some 192)) else d652 (change p 193 (some 192))) = d1093 p
  rw [sub2269, sub2268]
  rfl
theorem sub2271 (p : Pattern) : d655 (change p 193 (some 192)) = d1094 p := by
  change (if p 134 then d627 (change p 193 (some 192)) else d654 (change p 193 (some 192))) = d1094 p
  rw [sub2243, sub2270]
  rfl
theorem sub2272 (p : Pattern) : d656 (change p 193 (some 192)) = d1095 p := by
  change (if p 133 then d627 (change p 193 (some 192)) else d655 (change p 193 (some 192))) = d1095 p
  rw [sub2243, sub2271]
  rfl
theorem sub2273 (p : Pattern) : d657 (change p 193 (some 192)) = d1096 p := by
  change (if p 132 then d656 (change p 193 (some 192)) else d651 (change p 193 (some 192))) = d1096 p
  rw [sub2272, sub2267]
  rfl
theorem sub2274 (p : Pattern) : d658 (change p 193 (some 192)) = d1097 p := by
  change (if p 108 then d657 (change p 193 (some 192)) else d629 (change p 193 (some 192))) = d1097 p
  rw [sub2273, sub2245]
  rfl
theorem sub2275 (p : Pattern) : d0 (change p 10000 (some 158)) = d0 p := by
  rfl
theorem sub2276 (p : Pattern) : d2 (change p 10000 (some 158)) = d2 p := by
  rfl
theorem sub2277 (p : Pattern) : d6 (change p 10000 (some 158)) = d6 p := by
  change (if p 193 then d2 (change p 10000 (some 158)) else d0 (change p 10000 (some 158))) = d6 p
  rw [sub2276, sub2275]
  rfl
theorem sub2278 (p : Pattern) : d7 (change p 10000 (some 158)) = d7 p := by
  change (if p 192 then d6 (change p 10000 (some 158)) else d0 (change p 10000 (some 158))) = d7 p
  rw [sub2277, sub2275]
  rfl
theorem sub2279 (p : Pattern) : d4 (change p 10000 (some 158)) = d4 p := by
  rfl
end NetHack.Sokoban12CostPartition
