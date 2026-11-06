/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions17
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2160 (p : Pattern) : d500 (change p 116 (some 138)) = d87 p := by
  change d88 (change p 116 (some 138)) = d87 p
  exact sub2158 p
theorem sub2161 (p : Pattern) : d501 (change p 116 (some 138)) = d87 p := by
  change (if p 115 then d500 (change p 116 (some 138)) else d499 (change p 116 (some 138))) = d87 p
  rw [sub2160, sub2159]
  simp only [ite_self]
theorem sub2162 (p : Pattern) : d502 (change p 116 (some 138)) = d87 p := by
  change d88 (change p 116 (some 138)) = d87 p
  exact sub2158 p
theorem sub2163 (p : Pattern) : d503 (change p 116 (some 138)) = d87 p := by
  change d88 (change p 116 (some 138)) = d87 p
  exact sub2158 p
theorem sub2164 (p : Pattern) : d504 (change p 116 (some 138)) = d87 p := by
  change (if p 115 then d503 (change p 116 (some 138)) else d502 (change p 116 (some 138))) = d87 p
  rw [sub2163, sub2162]
  simp only [ite_self]
theorem sub2165 (p : Pattern) : d505 (change p 116 (some 138)) = d87 p := by
  change (if p 71 then d504 (change p 116 (some 138)) else d501 (change p 116 (some 138))) = d87 p
  rw [sub2164, sub2161]
  simp only [ite_self]
theorem sub2166 (p : Pattern) : d1 (change p 116 (some 138)) = d1 p := by
  rfl
theorem sub2167 (p : Pattern) : d102 (change p 116 (some 138)) = d102 p := by
  change (if p 247 then d12 (change p 116 (some 138)) else d1 (change p 116 (some 138))) = d102 p
  rw [sub2102, sub2166]
  rfl
theorem sub2168 (p : Pattern) : d103 (change p 116 (some 138)) = d103 p := by
  change (if p 246 then d102 (change p 116 (some 138)) else d1 (change p 116 (some 138))) = d103 p
  rw [sub2167, sub2166]
  rfl
theorem sub2169 (p : Pattern) : d104 (change p 116 (some 138)) = d104 p := by
  change (if p 204 then d12 (change p 116 (some 138)) else d103 (change p 116 (some 138))) = d104 p
  rw [sub2102, sub2168]
  rfl
theorem sub2170 (p : Pattern) : d105 (change p 116 (some 138)) = d105 p := by
  change (if p 182 then d104 (change p 116 (some 138)) else d103 (change p 116 (some 138))) = d105 p
  rw [sub2169, sub2168]
  rfl
theorem sub2171 (p : Pattern) : d5 (change p 116 (some 138)) = d5 p := by
  rfl
theorem sub2172 (p : Pattern) : d106 (change p 116 (some 138)) = d106 p := by
  change (if p 247 then d12 (change p 116 (some 138)) else d5 (change p 116 (some 138))) = d106 p
  rw [sub2102, sub2171]
  rfl
theorem sub2173 (p : Pattern) : d107 (change p 116 (some 138)) = d107 p := by
  change (if p 246 then d106 (change p 116 (some 138)) else d5 (change p 116 (some 138))) = d107 p
  rw [sub2172, sub2171]
  rfl
theorem sub2174 (p : Pattern) : d108 (change p 116 (some 138)) = d108 p := by
  change (if p 204 then d12 (change p 116 (some 138)) else d107 (change p 116 (some 138))) = d108 p
  rw [sub2102, sub2173]
  rfl
theorem sub2175 (p : Pattern) : d109 (change p 116 (some 138)) = d109 p := by
  change (if p 182 then d108 (change p 116 (some 138)) else d107 (change p 116 (some 138))) = d109 p
  rw [sub2174, sub2173]
  rfl
theorem sub2176 (p : Pattern) : d110 (change p 116 (some 138)) = d110 p := by
  change (if p 163 then d109 (change p 116 (some 138)) else d105 (change p 116 (some 138))) = d110 p
  rw [sub2175, sub2170]
  rfl
theorem sub2177 (p : Pattern) : d111 (change p 116 (some 138)) = d111 p := by
  change (if p 162 then d110 (change p 116 (some 138)) else d105 (change p 116 (some 138))) = d111 p
  rw [sub2176, sub2170]
  rfl
theorem sub2178 (p : Pattern) : d112 (change p 116 (some 138)) = d112 p := by
  change (if p 163 then d12 (change p 116 (some 138)) else d60 (change p 116 (some 138))) = d112 p
  rw [sub2102, sub2149]
  rfl
theorem sub2179 (p : Pattern) : d113 (change p 116 (some 138)) = d113 p := by
  change (if p 162 then d112 (change p 116 (some 138)) else d110 (change p 116 (some 138))) = d113 p
  rw [sub2178, sub2176]
  rfl
theorem sub2180 (p : Pattern) : d114 (change p 116 (some 138)) = d114 p := by
  change (if p 161 then d113 (change p 116 (some 138)) else d111 (change p 116 (some 138))) = d114 p
  rw [sub2179, sub2177]
  rfl
theorem sub2181 (p : Pattern) : d3 (change p 116 (some 138)) = d3 p := by
  rfl
theorem sub2182 (p : Pattern) : d115 (change p 116 (some 138)) = d115 p := by
  change (if p 247 then d12 (change p 116 (some 138)) else d3 (change p 116 (some 138))) = d115 p
  rw [sub2102, sub2181]
  rfl
theorem sub2183 (p : Pattern) : d116 (change p 116 (some 138)) = d116 p := by
  change (if p 246 then d115 (change p 116 (some 138)) else d3 (change p 116 (some 138))) = d116 p
  rw [sub2182, sub2181]
  rfl
theorem sub2184 (p : Pattern) : d117 (change p 116 (some 138)) = d117 p := by
  change (if p 204 then d12 (change p 116 (some 138)) else d116 (change p 116 (some 138))) = d117 p
  rw [sub2102, sub2183]
  rfl
theorem sub2185 (p : Pattern) : d132 (change p 116 (some 138)) = d132 p := by
  change (if p 182 then d117 (change p 116 (some 138)) else d116 (change p 116 (some 138))) = d132 p
  rw [sub2184, sub2183]
  rfl
theorem sub2186 (p : Pattern) : d7 (change p 116 (some 138)) = d7 p := by
  rfl
theorem sub2187 (p : Pattern) : d119 (change p 116 (some 138)) = d119 p := by
  change (if p 247 then d12 (change p 116 (some 138)) else d7 (change p 116 (some 138))) = d119 p
  rw [sub2102, sub2186]
  rfl
theorem sub2188 (p : Pattern) : d120 (change p 116 (some 138)) = d120 p := by
  change (if p 246 then d119 (change p 116 (some 138)) else d7 (change p 116 (some 138))) = d120 p
  rw [sub2187, sub2186]
  rfl
theorem sub2189 (p : Pattern) : d121 (change p 116 (some 138)) = d121 p := by
  change (if p 204 then d12 (change p 116 (some 138)) else d120 (change p 116 (some 138))) = d121 p
  rw [sub2102, sub2188]
  rfl
theorem sub2190 (p : Pattern) : d148 (change p 116 (some 138)) = d148 p := by
  change (if p 182 then d121 (change p 116 (some 138)) else d120 (change p 116 (some 138))) = d148 p
  rw [sub2189, sub2188]
  rfl
theorem sub2191 (p : Pattern) : d149 (change p 116 (some 138)) = d149 p := by
  change (if p 163 then d148 (change p 116 (some 138)) else d132 (change p 116 (some 138))) = d149 p
  rw [sub2190, sub2185]
  rfl
theorem sub2192 (p : Pattern) : d150 (change p 116 (some 138)) = d150 p := by
  change (if p 162 then d12 (change p 116 (some 138)) else d149 (change p 116 (some 138))) = d150 p
  rw [sub2102, sub2191]
  rfl
theorem sub2193 (p : Pattern) : d151 (change p 116 (some 138)) = d151 p := by
  change (if p 161 then d12 (change p 116 (some 138)) else d150 (change p 116 (some 138))) = d151 p
  rw [sub2102, sub2192]
  rfl
theorem sub2194 (p : Pattern) : d152 (change p 116 (some 138)) = d152 p := by
  change (if p 160 then d151 (change p 116 (some 138)) else d114 (change p 116 (some 138))) = d152 p
  rw [sub2193, sub2180]
  rfl
theorem sub2195 (p : Pattern) : d133 (change p 116 (some 138)) = d133 p := by
  change (if p 163 then d132 (change p 116 (some 138)) else d105 (change p 116 (some 138))) = d133 p
  rw [sub2185, sub2170]
  rfl
theorem sub2196 (p : Pattern) : d134 (change p 116 (some 138)) = d134 p := by
  change (if p 163 then d60 (change p 116 (some 138)) else d109 (change p 116 (some 138))) = d134 p
  rw [sub2149, sub2175]
  rfl
theorem sub2197 (p : Pattern) : d135 (change p 116 (some 138)) = d135 p := by
  change (if p 162 then d134 (change p 116 (some 138)) else d133 (change p 116 (some 138))) = d135 p
  rw [sub2196, sub2195]
  rfl
theorem sub2198 (p : Pattern) : d136 (change p 116 (some 138)) = d136 p := by
  change (if p 163 then d62 (change p 116 (some 138)) else d109 (change p 116 (some 138))) = d136 p
  rw [sub2137, sub2175]
  rfl
theorem sub2199 (p : Pattern) : d137 (change p 116 (some 138)) = d137 p := by
  change (if p 162 then d12 (change p 116 (some 138)) else d136 (change p 116 (some 138))) = d137 p
  rw [sub2102, sub2198]
  rfl
theorem sub2200 (p : Pattern) : d138 (change p 116 (some 138)) = d138 p := by
  change (if p 161 then d137 (change p 116 (some 138)) else d135 (change p 116 (some 138))) = d138 p
  rw [sub2199, sub2197]
  rfl
theorem sub2201 (p : Pattern) : d153 (change p 116 (some 138)) = d153 p := by
  change (if p 163 then d12 (change p 116 (some 138)) else d148 (change p 116 (some 138))) = d153 p
  rw [sub2102, sub2190]
  rfl
theorem sub2202 (p : Pattern) : d154 (change p 116 (some 138)) = d154 p := by
  change (if p 162 then d12 (change p 116 (some 138)) else d153 (change p 116 (some 138))) = d154 p
  rw [sub2102, sub2201]
  rfl
theorem sub2203 (p : Pattern) : d155 (change p 116 (some 138)) = d155 p := by
  change (if p 161 then d12 (change p 116 (some 138)) else d154 (change p 116 (some 138))) = d155 p
  rw [sub2102, sub2202]
  rfl
theorem sub2204 (p : Pattern) : d156 (change p 116 (some 138)) = d156 p := by
  change (if p 160 then d155 (change p 116 (some 138)) else d138 (change p 116 (some 138))) = d156 p
  rw [sub2203, sub2200]
  rfl
theorem sub2205 (p : Pattern) : d157 (change p 116 (some 138)) = d157 p := by
  change (if p 141 then d156 (change p 116 (some 138)) else d152 (change p 116 (some 138))) = d157 p
  rw [sub2204, sub2194]
  rfl
theorem sub2206 (p : Pattern) : d158 (change p 116 (some 138)) = d157 p := by
  change d157 (change p 116 (some 138)) = d157 p
  exact sub2205 p
theorem sub2207 (p : Pattern) : d506 (change p 116 (some 138)) = d157 p := by
  change d158 (change p 116 (some 138)) = d157 p
  exact sub2206 p
theorem sub2208 (p : Pattern) : d507 (change p 116 (some 138)) = d157 p := by
  change d158 (change p 116 (some 138)) = d157 p
  exact sub2206 p
theorem sub2209 (p : Pattern) : d508 (change p 116 (some 138)) = d157 p := by
  change (if p 115 then d507 (change p 116 (some 138)) else d506 (change p 116 (some 138))) = d157 p
  rw [sub2208, sub2207]
  simp only [ite_self]
theorem sub2210 (p : Pattern) : d509 (change p 116 (some 138)) = d4070 p := by
  change (if p 71 then d508 (change p 116 (some 138)) else d501 (change p 116 (some 138))) = d4070 p
  rw [sub2209, sub2161]
  rfl
theorem sub2211 (p : Pattern) : d510 (change p 116 (some 138)) = d4071 p := by
  change (if p 49 then d509 (change p 116 (some 138)) else d505 (change p 116 (some 138))) = d4071 p
  rw [sub2210, sub2165]
  rfl
theorem sub2212 (p : Pattern) : d211 (change p 116 (some 138)) = d211 p := by
  change (if p 163 then d12 (change p 116 (some 138)) else d109 (change p 116 (some 138))) = d211 p
  rw [sub2102, sub2175]
  rfl
theorem sub2213 (p : Pattern) : d212 (change p 116 (some 138)) = d212 p := by
  change (if p 162 then d211 (change p 116 (some 138)) else d133 (change p 116 (some 138))) = d212 p
  rw [sub2212, sub2195]
  rfl
theorem sub2214 (p : Pattern) : d213 (change p 116 (some 138)) = d213 p := by
  change (if p 162 then d12 (change p 116 (some 138)) else d211 (change p 116 (some 138))) = d213 p
  rw [sub2102, sub2212]
  rfl
theorem sub2215 (p : Pattern) : d214 (change p 116 (some 138)) = d214 p := by
  change (if p 161 then d213 (change p 116 (some 138)) else d212 (change p 116 (some 138))) = d214 p
  rw [sub2214, sub2213]
  rfl
theorem sub2216 (p : Pattern) : d221 (change p 116 (some 138)) = d221 p := by
  change (if p 160 then d155 (change p 116 (some 138)) else d214 (change p 116 (some 138))) = d221 p
  rw [sub2203, sub2215]
  rfl
theorem sub2217 (p : Pattern) : d222 (change p 116 (some 138)) = d222 p := by
  change (if p 141 then d221 (change p 116 (some 138)) else d152 (change p 116 (some 138))) = d222 p
  rw [sub2216, sub2194]
  rfl
theorem sub2218 (p : Pattern) : d223 (change p 116 (some 138)) = d222 p := by
  change d222 (change p 116 (some 138)) = d222 p
  exact sub2217 p
theorem sub2219 (p : Pattern) : d511 (change p 116 (some 138)) = d222 p := by
  change d223 (change p 116 (some 138)) = d222 p
  exact sub2218 p
theorem sub2220 (p : Pattern) : d268 (change p 116 (some 138)) = d268 p := by
  change (if p 204 then d116 (change p 116 (some 138)) else d103 (change p 116 (some 138))) = d268 p
  rw [sub2183, sub2168]
  rfl
theorem sub2221 (p : Pattern) : d269 (change p 116 (some 138)) = d269 p := by
  change (if p 182 then d117 (change p 116 (some 138)) else d268 (change p 116 (some 138))) = d269 p
  rw [sub2184, sub2220]
  rfl
theorem sub2222 (p : Pattern) : d291 (change p 116 (some 138)) = d291 p := by
  change (if p 163 then d269 (change p 116 (some 138)) else d105 (change p 116 (some 138))) = d291 p
  rw [sub2221, sub2170]
  rfl
theorem sub2223 (p : Pattern) : d273 (change p 116 (some 138)) = d273 p := by
  change (if p 204 then d120 (change p 116 (some 138)) else d107 (change p 116 (some 138))) = d273 p
  rw [sub2188, sub2173]
  rfl
theorem sub2224 (p : Pattern) : d292 (change p 116 (some 138)) = d292 p := by
  change (if p 182 then d121 (change p 116 (some 138)) else d273 (change p 116 (some 138))) = d292 p
  rw [sub2189, sub2223]
  rfl
theorem sub2225 (p : Pattern) : d293 (change p 116 (some 138)) = d293 p := by
  change (if p 163 then d292 (change p 116 (some 138)) else d269 (change p 116 (some 138))) = d293 p
  rw [sub2224, sub2221]
  rfl
theorem sub2226 (p : Pattern) : d294 (change p 116 (some 138)) = d294 p := by
  change (if p 162 then d293 (change p 116 (some 138)) else d291 (change p 116 (some 138))) = d294 p
  rw [sub2225, sub2222]
  rfl
theorem sub2227 (p : Pattern) : d277 (change p 116 (some 138)) = d277 p := by
  change (if p 182 then d12 (change p 116 (some 138)) else d59 (change p 116 (some 138))) = d277 p
  rw [sub2102, sub2148]
  rfl
theorem sub2228 (p : Pattern) : d278 (change p 116 (some 138)) = d278 p := by
  change (if p 163 then d12 (change p 116 (some 138)) else d277 (change p 116 (some 138))) = d278 p
  rw [sub2102, sub2227]
  rfl
theorem sub2229 (p : Pattern) : d295 (change p 116 (some 138)) = d295 p := by
  change (if p 162 then d278 (change p 116 (some 138)) else d293 (change p 116 (some 138))) = d295 p
  rw [sub2228, sub2225]
  rfl
theorem sub2230 (p : Pattern) : d296 (change p 116 (some 138)) = d296 p := by
  change (if p 161 then d295 (change p 116 (some 138)) else d294 (change p 116 (some 138))) = d296 p
  rw [sub2229, sub2226]
  rfl
theorem sub2231 (p : Pattern) : d297 (change p 116 (some 138)) = d297 p := by
  change (if p 160 then d151 (change p 116 (some 138)) else d296 (change p 116 (some 138))) = d297 p
  rw [sub2193, sub2230]
  rfl
theorem sub2232 (p : Pattern) : d282 (change p 116 (some 138)) = d282 p := by
  change (if p 204 then d107 (change p 116 (some 138)) else d116 (change p 116 (some 138))) = d282 p
  rw [sub2173, sub2183]
  rfl
theorem sub2233 (p : Pattern) : d298 (change p 116 (some 138)) = d298 p := by
  change (if p 182 then d108 (change p 116 (some 138)) else d282 (change p 116 (some 138))) = d298 p
  rw [sub2174, sub2232]
  rfl
theorem sub2234 (p : Pattern) : d299 (change p 116 (some 138)) = d299 p := by
  change (if p 163 then d298 (change p 116 (some 138)) else d269 (change p 116 (some 138))) = d299 p
  rw [sub2233, sub2221]
  rfl
theorem sub2235 (p : Pattern) : d300 (change p 116 (some 138)) = d300 p := by
  change (if p 163 then d12 (change p 116 (some 138)) else d292 (change p 116 (some 138))) = d300 p
  rw [sub2102, sub2224]
  rfl
theorem sub2236 (p : Pattern) : d301 (change p 116 (some 138)) = d301 p := by
  change (if p 162 then d300 (change p 116 (some 138)) else d299 (change p 116 (some 138))) = d301 p
  rw [sub2235, sub2234]
  rfl
theorem sub2237 (p : Pattern) : d302 (change p 116 (some 138)) = d302 p := by
  change (if p 162 then d12 (change p 116 (some 138)) else d300 (change p 116 (some 138))) = d302 p
  rw [sub2102, sub2235]
  rfl
theorem sub2238 (p : Pattern) : d303 (change p 116 (some 138)) = d303 p := by
  change (if p 161 then d302 (change p 116 (some 138)) else d301 (change p 116 (some 138))) = d303 p
  rw [sub2237, sub2236]
  rfl
theorem sub2239 (p : Pattern) : d304 (change p 116 (some 138)) = d304 p := by
  change (if p 160 then d155 (change p 116 (some 138)) else d303 (change p 116 (some 138))) = d304 p
  rw [sub2203, sub2238]
  rfl
theorem sub2240 (p : Pattern) : d305 (change p 116 (some 138)) = d305 p := by
  change (if p 141 then d304 (change p 116 (some 138)) else d297 (change p 116 (some 138))) = d305 p
  rw [sub2239, sub2231]
  rfl
theorem sub2241 (p : Pattern) : d306 (change p 116 (some 138)) = d305 p := by
  change d305 (change p 116 (some 138)) = d305 p
  exact sub2240 p
theorem sub2242 (p : Pattern) : d512 (change p 116 (some 138)) = d305 p := by
  change d306 (change p 116 (some 138)) = d305 p
  exact sub2241 p
theorem sub2243 (p : Pattern) : d513 (change p 116 (some 138)) = d4072 p := by
  change (if p 115 then d512 (change p 116 (some 138)) else d511 (change p 116 (some 138))) = d4072 p
  rw [sub2242, sub2219]
  rfl
theorem sub2244 (p : Pattern) : d514 (change p 116 (some 138)) = d4073 p := by
  change (if p 71 then d513 (change p 116 (some 138)) else d501 (change p 116 (some 138))) = d4073 p
  rw [sub2243, sub2161]
  rfl
theorem sub2245 (p : Pattern) : d515 (change p 116 (some 138)) = d4074 p := by
  change (if p 49 then d514 (change p 116 (some 138)) else d505 (change p 116 (some 138))) = d4074 p
  rw [sub2244, sub2165]
  rfl
theorem sub2246 (p : Pattern) : d516 (change p 116 (some 138)) = d4075 p := by
  change (if p 48 then d515 (change p 116 (some 138)) else d510 (change p 116 (some 138))) = d4075 p
  rw [sub2245, sub2211]
  rfl
theorem sub2247 (p : Pattern) : d0 (change p 10000 (some 141)) = d0 p := by
  rfl
theorem sub2248 (p : Pattern) : d12 (change p 10000 (some 141)) = d12 p := by
  rfl
theorem sub2249 (p : Pattern) : d13 (change p 10000 (some 141)) = d13 p := by
  change (if p 247 then d12 (change p 10000 (some 141)) else d0 (change p 10000 (some 141))) = d13 p
  rw [sub2248, sub2247]
  rfl
theorem sub2250 (p : Pattern) : d14 (change p 10000 (some 141)) = d14 p := by
  change (if p 246 then d13 (change p 10000 (some 141)) else d0 (change p 10000 (some 141))) = d14 p
  rw [sub2249, sub2247]
  rfl
theorem sub2251 (p : Pattern) : d15 (change p 10000 (some 141)) = d15 p := by
  change (if p 204 then d12 (change p 10000 (some 141)) else d14 (change p 10000 (some 141))) = d15 p
  rw [sub2248, sub2250]
  rfl
theorem sub2252 (p : Pattern) : d16 (change p 10000 (some 141)) = d16 p := by
  change (if p 182 then d15 (change p 10000 (some 141)) else d14 (change p 10000 (some 141))) = d16 p
  rw [sub2251, sub2250]
  rfl
theorem sub2253 (p : Pattern) : d2 (change p 10000 (some 141)) = d2 p := by
  rfl
theorem sub2254 (p : Pattern) : d30 (change p 10000 (some 141)) = d30 p := by
  change (if p 247 then d12 (change p 10000 (some 141)) else d2 (change p 10000 (some 141))) = d30 p
  rw [sub2248, sub2253]
  rfl
theorem sub2255 (p : Pattern) : d31 (change p 10000 (some 141)) = d31 p := by
  change (if p 246 then d30 (change p 10000 (some 141)) else d2 (change p 10000 (some 141))) = d31 p
  rw [sub2254, sub2253]
  rfl
theorem sub2256 (p : Pattern) : d32 (change p 10000 (some 141)) = d32 p := by
  change (if p 204 then d12 (change p 10000 (some 141)) else d31 (change p 10000 (some 141))) = d32 p
  rw [sub2248, sub2255]
  rfl
theorem sub2257 (p : Pattern) : d53 (change p 10000 (some 141)) = d53 p := by
  change (if p 182 then d32 (change p 10000 (some 141)) else d31 (change p 10000 (some 141))) = d53 p
  rw [sub2256, sub2255]
  rfl
theorem sub2258 (p : Pattern) : d54 (change p 10000 (some 141)) = d54 p := by
  change (if p 163 then d53 (change p 10000 (some 141)) else d16 (change p 10000 (some 141))) = d54 p
  rw [sub2257, sub2252]
  rfl
theorem sub2259 (p : Pattern) : d4 (change p 10000 (some 141)) = d4 p := by
  rfl
theorem sub2260 (p : Pattern) : d17 (change p 10000 (some 141)) = d17 p := by
  change (if p 247 then d12 (change p 10000 (some 141)) else d4 (change p 10000 (some 141))) = d17 p
  rw [sub2248, sub2259]
  rfl
theorem sub2261 (p : Pattern) : d18 (change p 10000 (some 141)) = d18 p := by
  change (if p 246 then d17 (change p 10000 (some 141)) else d4 (change p 10000 (some 141))) = d18 p
  rw [sub2260, sub2259]
  rfl
theorem sub2262 (p : Pattern) : d19 (change p 10000 (some 141)) = d19 p := by
  change (if p 204 then d12 (change p 10000 (some 141)) else d18 (change p 10000 (some 141))) = d19 p
  rw [sub2248, sub2261]
  rfl
theorem sub2263 (p : Pattern) : d20 (change p 10000 (some 141)) = d20 p := by
  change (if p 182 then d19 (change p 10000 (some 141)) else d18 (change p 10000 (some 141))) = d20 p
  rw [sub2262, sub2261]
  rfl
theorem sub2264 (p : Pattern) : d9 (change p 10000 (some 141)) = d9 p := by
  rfl
theorem sub2265 (p : Pattern) : d23 (change p 10000 (some 141)) = d23 p := by
  change (if p 247 then d12 (change p 10000 (some 141)) else d9 (change p 10000 (some 141))) = d23 p
  rw [sub2248, sub2264]
  rfl
theorem sub2266 (p : Pattern) : d24 (change p 10000 (some 141)) = d24 p := by
  change (if p 246 then d23 (change p 10000 (some 141)) else d9 (change p 10000 (some 141))) = d24 p
  rw [sub2265, sub2264]
  rfl
theorem sub2267 (p : Pattern) : d25 (change p 10000 (some 141)) = d25 p := by
  change (if p 204 then d12 (change p 10000 (some 141)) else d24 (change p 10000 (some 141))) = d25 p
  rw [sub2248, sub2266]
  rfl
theorem sub2268 (p : Pattern) : d26 (change p 10000 (some 141)) = d26 p := by
  change (if p 182 then d25 (change p 10000 (some 141)) else d24 (change p 10000 (some 141))) = d26 p
  rw [sub2267, sub2266]
  rfl
theorem sub2269 (p : Pattern) : d55 (change p 10000 (some 141)) = d55 p := by
  change (if p 163 then d26 (change p 10000 (some 141)) else d20 (change p 10000 (some 141))) = d55 p
  rw [sub2268, sub2263]
  rfl
theorem sub2270 (p : Pattern) : d56 (change p 10000 (some 141)) = d56 p := by
  change (if p 162 then d55 (change p 10000 (some 141)) else d54 (change p 10000 (some 141))) = d56 p
  rw [sub2269, sub2258]
  rfl
theorem sub2271 (p : Pattern) : d10 (change p 10000 (some 141)) = d10 p := by
  rfl
theorem sub2272 (p : Pattern) : d57 (change p 10000 (some 141)) = d57 p := by
  change (if p 247 then d12 (change p 10000 (some 141)) else d10 (change p 10000 (some 141))) = d57 p
  rw [sub2248, sub2271]
  rfl
theorem sub2273 (p : Pattern) : d58 (change p 10000 (some 141)) = d58 p := by
  change (if p 246 then d57 (change p 10000 (some 141)) else d10 (change p 10000 (some 141))) = d58 p
  rw [sub2272, sub2271]
  rfl
theorem sub2274 (p : Pattern) : d59 (change p 10000 (some 141)) = d59 p := by
  change (if p 204 then d12 (change p 10000 (some 141)) else d58 (change p 10000 (some 141))) = d59 p
  rw [sub2248, sub2273]
  rfl
theorem sub2275 (p : Pattern) : d60 (change p 10000 (some 141)) = d60 p := by
  change (if p 182 then d59 (change p 10000 (some 141)) else d58 (change p 10000 (some 141))) = d60 p
  rw [sub2274, sub2273]
  rfl
theorem sub2276 (p : Pattern) : d61 (change p 10000 (some 141)) = d61 p := by
  change (if p 163 then d60 (change p 10000 (some 141)) else d20 (change p 10000 (some 141))) = d61 p
  rw [sub2275, sub2263]
  rfl
theorem sub2277 (p : Pattern) : d11 (change p 10000 (some 141)) = d11 p := by
  rfl
theorem sub2278 (p : Pattern) : d39 (change p 10000 (some 141)) = d39 p := by
  change (if p 247 then d12 (change p 10000 (some 141)) else d11 (change p 10000 (some 141))) = d39 p
  rw [sub2248, sub2277]
  rfl
theorem sub2279 (p : Pattern) : d40 (change p 10000 (some 141)) = d40 p := by
  change (if p 246 then d39 (change p 10000 (some 141)) else d11 (change p 10000 (some 141))) = d40 p
  rw [sub2278, sub2277]
  rfl
end NetHack.Sokoban22Refined85
