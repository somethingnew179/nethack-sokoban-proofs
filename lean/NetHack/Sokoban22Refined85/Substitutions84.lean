/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions83
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub10080 (p : Pattern) : d2199 (change p 224 none) = d21 p := by
  change (if p 163 then d2198 (change p 224 none) else d2195 (change p 224 none)) = d21 p
  rw [sub10079, sub10073]
  rfl
theorem sub10081 (p : Pattern) : d2200 (change p 224 none) = d22 p := by
  change (if p 162 then d2199 (change p 224 none) else d2192 (change p 224 none)) = d22 p
  rw [sub10080, sub10070]
  rfl
theorem sub10082 (p : Pattern) : d2201 (change p 224 none) = d16 p := by
  change (if p 182 then d2187 (change p 224 none) else d2185 (change p 224 none)) = d16 p
  rw [sub10065, sub10063]
  rfl
theorem sub10083 (p : Pattern) : d2202 (change p 224 none) = d21 p := by
  change (if p 163 then d2198 (change p 224 none) else d2201 (change p 224 none)) = d21 p
  rw [sub10079, sub10082]
  rfl
theorem sub10084 (p : Pattern) : d9 (change p 224 none) = d9 p := by
  rfl
theorem sub10085 (p : Pattern) : d23 (change p 224 none) = d23 p := by
  change (if p 247 then d12 (change p 224 none) else d9 (change p 224 none)) = d23 p
  rw [sub10059, sub10084]
  rfl
theorem sub10086 (p : Pattern) : d24 (change p 224 none) = d24 p := by
  change (if p 246 then d23 (change p 224 none) else d9 (change p 224 none)) = d24 p
  rw [sub10085, sub10084]
  rfl
theorem sub10087 (p : Pattern) : d2203 (change p 224 none) = d24 p := by
  change d24 (change p 224 none) = d24 p
  exact sub10086 p
theorem sub10088 (p : Pattern) : d2204 (change p 224 none) = d25 p := by
  change (if p 204 then d12 (change p 224 none) else d2203 (change p 224 none)) = d25 p
  rw [sub10059, sub10087]
  rfl
theorem sub10089 (p : Pattern) : d2205 (change p 224 none) = d26 p := by
  change (if p 182 then d2204 (change p 224 none) else d2203 (change p 224 none)) = d26 p
  rw [sub10088, sub10087]
  rfl
theorem sub10090 (p : Pattern) : d2206 (change p 224 none) = d27 p := by
  change (if p 163 then d12 (change p 224 none) else d2205 (change p 224 none)) = d27 p
  rw [sub10059, sub10089]
  rfl
theorem sub10091 (p : Pattern) : d2207 (change p 224 none) = d28 p := by
  change (if p 162 then d2206 (change p 224 none) else d2202 (change p 224 none)) = d28 p
  rw [sub10090, sub10083]
  rfl
theorem sub10092 (p : Pattern) : d2208 (change p 224 none) = d29 p := by
  change (if p 161 then d2207 (change p 224 none) else d2200 (change p 224 none)) = d29 p
  rw [sub10091, sub10081]
  rfl
theorem sub10093 (p : Pattern) : d2 (change p 224 none) = d2 p := by
  rfl
theorem sub10094 (p : Pattern) : d30 (change p 224 none) = d30 p := by
  change (if p 247 then d12 (change p 224 none) else d2 (change p 224 none)) = d30 p
  rw [sub10059, sub10093]
  rfl
theorem sub10095 (p : Pattern) : d31 (change p 224 none) = d31 p := by
  change (if p 246 then d30 (change p 224 none) else d2 (change p 224 none)) = d31 p
  rw [sub10094, sub10093]
  rfl
theorem sub10096 (p : Pattern) : d2209 (change p 224 none) = d31 p := by
  change d31 (change p 224 none) = d31 p
  exact sub10095 p
theorem sub10097 (p : Pattern) : d2210 (change p 224 none) = d32 p := by
  change (if p 204 then d12 (change p 224 none) else d2209 (change p 224 none)) = d32 p
  rw [sub10059, sub10096]
  rfl
theorem sub10098 (p : Pattern) : d2211 (change p 224 none) = d33 p := by
  change (if p 182 then d2210 (change p 224 none) else d2185 (change p 224 none)) = d33 p
  rw [sub10097, sub10063]
  rfl
theorem sub10099 (p : Pattern) : d6 (change p 224 none) = d6 p := by
  rfl
theorem sub10100 (p : Pattern) : d34 (change p 224 none) = d34 p := by
  change (if p 247 then d12 (change p 224 none) else d6 (change p 224 none)) = d34 p
  rw [sub10059, sub10099]
  rfl
theorem sub10101 (p : Pattern) : d35 (change p 224 none) = d35 p := by
  change (if p 246 then d34 (change p 224 none) else d6 (change p 224 none)) = d35 p
  rw [sub10100, sub10099]
  rfl
theorem sub10102 (p : Pattern) : d2212 (change p 224 none) = d35 p := by
  change d35 (change p 224 none) = d35 p
  exact sub10101 p
theorem sub10103 (p : Pattern) : d2213 (change p 224 none) = d36 p := by
  change (if p 204 then d12 (change p 224 none) else d2212 (change p 224 none)) = d36 p
  rw [sub10059, sub10102]
  rfl
theorem sub10104 (p : Pattern) : d2214 (change p 224 none) = d37 p := by
  change (if p 182 then d2213 (change p 224 none) else d2185 (change p 224 none)) = d37 p
  rw [sub10103, sub10063]
  rfl
theorem sub10105 (p : Pattern) : d2215 (change p 224 none) = d38 p := by
  change (if p 163 then d2214 (change p 224 none) else d2211 (change p 224 none)) = d38 p
  rw [sub10104, sub10098]
  rfl
theorem sub10106 (p : Pattern) : d11 (change p 224 none) = d11 p := by
  rfl
theorem sub10107 (p : Pattern) : d39 (change p 224 none) = d39 p := by
  change (if p 247 then d12 (change p 224 none) else d11 (change p 224 none)) = d39 p
  rw [sub10059, sub10106]
  rfl
theorem sub10108 (p : Pattern) : d40 (change p 224 none) = d40 p := by
  change (if p 246 then d39 (change p 224 none) else d11 (change p 224 none)) = d40 p
  rw [sub10107, sub10106]
  rfl
theorem sub10109 (p : Pattern) : d2216 (change p 224 none) = d40 p := by
  change d40 (change p 224 none) = d40 p
  exact sub10108 p
theorem sub10110 (p : Pattern) : d2217 (change p 224 none) = d41 p := by
  change (if p 204 then d12 (change p 224 none) else d2216 (change p 224 none)) = d41 p
  rw [sub10059, sub10109]
  rfl
theorem sub10111 (p : Pattern) : d2218 (change p 224 none) = d42 p := by
  change (if p 182 then d2217 (change p 224 none) else d2185 (change p 224 none)) = d42 p
  rw [sub10110, sub10063]
  rfl
theorem sub10112 (p : Pattern) : d2219 (change p 224 none) = d43 p := by
  change (if p 182 then d12 (change p 224 none) else d2196 (change p 224 none)) = d43 p
  rw [sub10059, sub10077]
  rfl
theorem sub10113 (p : Pattern) : d2220 (change p 224 none) = d44 p := by
  change (if p 163 then d2219 (change p 224 none) else d2218 (change p 224 none)) = d44 p
  rw [sub10112, sub10111]
  rfl
theorem sub10114 (p : Pattern) : d2221 (change p 224 none) = d45 p := by
  change (if p 162 then d2220 (change p 224 none) else d2215 (change p 224 none)) = d45 p
  rw [sub10113, sub10105]
  rfl
theorem sub10115 (p : Pattern) : d2222 (change p 224 none) = d46 p := by
  change (if p 182 then d12 (change p 224 none) else d2185 (change p 224 none)) = d46 p
  rw [sub10059, sub10063]
  rfl
theorem sub10116 (p : Pattern) : d2223 (change p 224 none) = d47 p := by
  change (if p 163 then d2219 (change p 224 none) else d2222 (change p 224 none)) = d47 p
  rw [sub10112, sub10115]
  rfl
theorem sub10117 (p : Pattern) : d2224 (change p 224 none) = d48 p := by
  change (if p 182 then d12 (change p 224 none) else d2203 (change p 224 none)) = d48 p
  rw [sub10059, sub10087]
  rfl
theorem sub10118 (p : Pattern) : d2225 (change p 224 none) = d49 p := by
  change (if p 163 then d12 (change p 224 none) else d2224 (change p 224 none)) = d49 p
  rw [sub10059, sub10117]
  rfl
theorem sub10119 (p : Pattern) : d2226 (change p 224 none) = d50 p := by
  change (if p 162 then d2225 (change p 224 none) else d2223 (change p 224 none)) = d50 p
  rw [sub10118, sub10116]
  rfl
theorem sub10120 (p : Pattern) : d2227 (change p 224 none) = d51 p := by
  change (if p 161 then d2226 (change p 224 none) else d2221 (change p 224 none)) = d51 p
  rw [sub10119, sub10114]
  rfl
theorem sub10121 (p : Pattern) : d2228 (change p 224 none) = d52 p := by
  change (if p 160 then d2227 (change p 224 none) else d2208 (change p 224 none)) = d52 p
  rw [sub10120, sub10092]
  rfl
theorem sub10122 (p : Pattern) : d2229 (change p 224 none) = d14 p := by
  change d14 (change p 224 none) = d14 p
  exact sub10061 p
theorem sub10123 (p : Pattern) : d2230 (change p 224 none) = d14 p := by
  change (if p 204 then d2185 (change p 224 none) else d2229 (change p 224 none)) = d14 p
  rw [sub10063, sub10122]
  simp only [ite_self]
theorem sub10124 (p : Pattern) : d2231 (change p 224 none) = d16 p := by
  change (if p 182 then d2187 (change p 224 none) else d2230 (change p 224 none)) = d16 p
  rw [sub10065, sub10123]
  rfl
theorem sub10125 (p : Pattern) : d2232 (change p 224 none) = d53 p := by
  change (if p 182 then d2210 (change p 224 none) else d2209 (change p 224 none)) = d53 p
  rw [sub10097, sub10096]
  rfl
theorem sub10126 (p : Pattern) : d2233 (change p 224 none) = d54 p := by
  change (if p 163 then d2232 (change p 224 none) else d2231 (change p 224 none)) = d54 p
  rw [sub10125, sub10124]
  rfl
theorem sub10127 (p : Pattern) : d2234 (change p 224 none) = d55 p := by
  change (if p 163 then d2205 (change p 224 none) else d2198 (change p 224 none)) = d55 p
  rw [sub10089, sub10079]
  rfl
theorem sub10128 (p : Pattern) : d2235 (change p 224 none) = d56 p := by
  change (if p 162 then d2234 (change p 224 none) else d2233 (change p 224 none)) = d56 p
  rw [sub10127, sub10126]
  rfl
theorem sub10129 (p : Pattern) : d10 (change p 224 none) = d10 p := by
  rfl
theorem sub10130 (p : Pattern) : d57 (change p 224 none) = d57 p := by
  change (if p 247 then d12 (change p 224 none) else d10 (change p 224 none)) = d57 p
  rw [sub10059, sub10129]
  rfl
theorem sub10131 (p : Pattern) : d58 (change p 224 none) = d58 p := by
  change (if p 246 then d57 (change p 224 none) else d10 (change p 224 none)) = d58 p
  rw [sub10130, sub10129]
  rfl
theorem sub10132 (p : Pattern) : d2236 (change p 224 none) = d58 p := by
  change d58 (change p 224 none) = d58 p
  exact sub10131 p
theorem sub10133 (p : Pattern) : d2237 (change p 224 none) = d59 p := by
  change (if p 204 then d12 (change p 224 none) else d2236 (change p 224 none)) = d59 p
  rw [sub10059, sub10132]
  rfl
theorem sub10134 (p : Pattern) : d2238 (change p 224 none) = d60 p := by
  change (if p 182 then d2237 (change p 224 none) else d2236 (change p 224 none)) = d60 p
  rw [sub10133, sub10132]
  rfl
theorem sub10135 (p : Pattern) : d2239 (change p 224 none) = d61 p := by
  change (if p 163 then d2238 (change p 224 none) else d2198 (change p 224 none)) = d61 p
  rw [sub10134, sub10079]
  rfl
theorem sub10136 (p : Pattern) : d2240 (change p 224 none) = d62 p := by
  change (if p 182 then d2217 (change p 224 none) else d2216 (change p 224 none)) = d62 p
  rw [sub10110, sub10109]
  rfl
theorem sub10137 (p : Pattern) : d2241 (change p 224 none) = d63 p := by
  change (if p 163 then d12 (change p 224 none) else d2240 (change p 224 none)) = d63 p
  rw [sub10059, sub10136]
  rfl
theorem sub10138 (p : Pattern) : d2242 (change p 224 none) = d64 p := by
  change (if p 162 then d2241 (change p 224 none) else d2239 (change p 224 none)) = d64 p
  rw [sub10137, sub10135]
  rfl
theorem sub10139 (p : Pattern) : d2243 (change p 224 none) = d65 p := by
  change (if p 161 then d2242 (change p 224 none) else d2235 (change p 224 none)) = d65 p
  rw [sub10138, sub10128]
  rfl
theorem sub10140 (p : Pattern) : d2244 (change p 224 none) = d66 p := by
  change (if p 182 then d12 (change p 224 none) else d2209 (change p 224 none)) = d66 p
  rw [sub10059, sub10096]
  rfl
theorem sub10141 (p : Pattern) : d2245 (change p 224 none) = d67 p := by
  change (if p 163 then d2244 (change p 224 none) else d2214 (change p 224 none)) = d67 p
  rw [sub10140, sub10104]
  rfl
theorem sub10142 (p : Pattern) : d2246 (change p 224 none) = d68 p := by
  change (if p 163 then d2224 (change p 224 none) else d2219 (change p 224 none)) = d68 p
  rw [sub10117, sub10112]
  rfl
theorem sub10143 (p : Pattern) : d2247 (change p 224 none) = d69 p := by
  change (if p 162 then d2246 (change p 224 none) else d2245 (change p 224 none)) = d69 p
  rw [sub10142, sub10141]
  rfl
theorem sub10144 (p : Pattern) : d2248 (change p 224 none) = d70 p := by
  change (if p 182 then d12 (change p 224 none) else d2236 (change p 224 none)) = d70 p
  rw [sub10059, sub10132]
  rfl
theorem sub10145 (p : Pattern) : d2249 (change p 224 none) = d71 p := by
  change (if p 163 then d2248 (change p 224 none) else d2219 (change p 224 none)) = d71 p
  rw [sub10144, sub10112]
  rfl
theorem sub10146 (p : Pattern) : d2250 (change p 224 none) = d72 p := by
  change (if p 182 then d12 (change p 224 none) else d2216 (change p 224 none)) = d72 p
  rw [sub10059, sub10109]
  rfl
theorem sub10147 (p : Pattern) : d2251 (change p 224 none) = d73 p := by
  change (if p 163 then d12 (change p 224 none) else d2250 (change p 224 none)) = d73 p
  rw [sub10059, sub10146]
  rfl
theorem sub10148 (p : Pattern) : d2252 (change p 224 none) = d74 p := by
  change (if p 162 then d2251 (change p 224 none) else d2249 (change p 224 none)) = d74 p
  rw [sub10147, sub10145]
  rfl
theorem sub10149 (p : Pattern) : d2253 (change p 224 none) = d75 p := by
  change (if p 161 then d2252 (change p 224 none) else d2247 (change p 224 none)) = d75 p
  rw [sub10148, sub10143]
  rfl
theorem sub10150 (p : Pattern) : d2254 (change p 224 none) = d76 p := by
  change (if p 160 then d2253 (change p 224 none) else d2243 (change p 224 none)) = d76 p
  rw [sub10149, sub10139]
  rfl
theorem sub10151 (p : Pattern) : d2255 (change p 224 none) = d77 p := by
  change (if p 141 then d2254 (change p 224 none) else d2228 (change p 224 none)) = d77 p
  rw [sub10150, sub10121]
  rfl
theorem sub10152 (p : Pattern) : d2256 (change p 224 none) = d22 p := by
  change (if p 162 then d2202 (change p 224 none) else d2201 (change p 224 none)) = d22 p
  rw [sub10083, sub10082]
  rfl
theorem sub10153 (p : Pattern) : d2257 (change p 224 none) = d29 p := by
  change (if p 161 then d2207 (change p 224 none) else d2256 (change p 224 none)) = d29 p
  rw [sub10091, sub10152]
  rfl
theorem sub10154 (p : Pattern) : d2258 (change p 224 none) = d78 p := by
  change (if p 182 then d2213 (change p 224 none) else d2212 (change p 224 none)) = d78 p
  rw [sub10103, sub10102]
  rfl
theorem sub10155 (p : Pattern) : d2259 (change p 224 none) = d79 p := by
  change (if p 163 then d2258 (change p 224 none) else d2232 (change p 224 none)) = d79 p
  rw [sub10154, sub10125]
  rfl
theorem sub10156 (p : Pattern) : d2260 (change p 224 none) = d80 p := by
  change (if p 162 then d2241 (change p 224 none) else d2259 (change p 224 none)) = d80 p
  rw [sub10137, sub10155]
  rfl
theorem sub10157 (p : Pattern) : d2261 (change p 224 none) = d81 p := by
  change (if p 161 then d12 (change p 224 none) else d2260 (change p 224 none)) = d81 p
  rw [sub10059, sub10156]
  rfl
theorem sub10158 (p : Pattern) : d2262 (change p 224 none) = d82 p := by
  change (if p 160 then d2261 (change p 224 none) else d2257 (change p 224 none)) = d82 p
  rw [sub10157, sub10153]
  rfl
theorem sub10159 (p : Pattern) : d2263 (change p 224 none) = d54 p := by
  change (if p 163 then d2232 (change p 224 none) else d2201 (change p 224 none)) = d54 p
  rw [sub10125, sub10082]
  rfl
theorem sub10160 (p : Pattern) : d2264 (change p 224 none) = d56 p := by
  change (if p 162 then d2234 (change p 224 none) else d2263 (change p 224 none)) = d56 p
  rw [sub10127, sub10159]
  rfl
theorem sub10161 (p : Pattern) : d2265 (change p 224 none) = d65 p := by
  change (if p 161 then d2242 (change p 224 none) else d2264 (change p 224 none)) = d65 p
  rw [sub10138, sub10160]
  rfl
theorem sub10162 (p : Pattern) : d2266 (change p 224 none) = d83 p := by
  change (if p 163 then d12 (change p 224 none) else d2258 (change p 224 none)) = d83 p
  rw [sub10059, sub10154]
  rfl
theorem sub10163 (p : Pattern) : d2267 (change p 224 none) = d84 p := by
  change (if p 162 then d12 (change p 224 none) else d2266 (change p 224 none)) = d84 p
  rw [sub10059, sub10162]
  rfl
theorem sub10164 (p : Pattern) : d2268 (change p 224 none) = d85 p := by
  change (if p 161 then d12 (change p 224 none) else d2267 (change p 224 none)) = d85 p
  rw [sub10059, sub10163]
  rfl
theorem sub10165 (p : Pattern) : d2269 (change p 224 none) = d86 p := by
  change (if p 160 then d2268 (change p 224 none) else d2265 (change p 224 none)) = d86 p
  rw [sub10164, sub10161]
  rfl
theorem sub10166 (p : Pattern) : d2270 (change p 224 none) = d87 p := by
  change (if p 141 then d2269 (change p 224 none) else d2262 (change p 224 none)) = d87 p
  rw [sub10165, sub10158]
  rfl
theorem sub10167 (p : Pattern) : d2271 (change p 224 none) = d88 p := by
  change (if p 138 then d2270 (change p 224 none) else d2255 (change p 224 none)) = d88 p
  rw [sub10166, sub10151]
  rfl
theorem sub10168 (p : Pattern) : d2272 (change p 224 none) = d16 p := by
  change (if p 163 then d2201 (change p 224 none) else d2195 (change p 224 none)) = d16 p
  rw [sub10082, sub10073]
  simp only [ite_self]
theorem sub10169 (p : Pattern) : d2273 (change p 224 none) = d22 p := by
  change (if p 162 then d2202 (change p 224 none) else d2272 (change p 224 none)) = d22 p
  rw [sub10083, sub10168]
  rfl
theorem sub10170 (p : Pattern) : d2274 (change p 224 none) = d29 p := by
  change (if p 161 then d2207 (change p 224 none) else d2273 (change p 224 none)) = d29 p
  rw [sub10091, sub10169]
  rfl
theorem sub10171 (p : Pattern) : d2275 (change p 224 none) = d82 p := by
  change (if p 160 then d2261 (change p 224 none) else d2274 (change p 224 none)) = d82 p
  rw [sub10157, sub10170]
  rfl
theorem sub10172 (p : Pattern) : d2276 (change p 224 none) = d87 p := by
  change (if p 141 then d2269 (change p 224 none) else d2275 (change p 224 none)) = d87 p
  rw [sub10165, sub10171]
  rfl
theorem sub10173 (p : Pattern) : d2277 (change p 224 none) = d89 p := by
  change (if p 163 then d2240 (change p 224 none) else d2205 (change p 224 none)) = d89 p
  rw [sub10136, sub10089]
  rfl
theorem sub10174 (p : Pattern) : d2278 (change p 224 none) = d90 p := by
  change (if p 162 then d2241 (change p 224 none) else d2277 (change p 224 none)) = d90 p
  rw [sub10137, sub10173]
  rfl
theorem sub10175 (p : Pattern) : d2279 (change p 224 none) = d91 p := by
  change (if p 162 then d12 (change p 224 none) else d2241 (change p 224 none)) = d91 p
  rw [sub10059, sub10137]
  rfl
theorem sub10176 (p : Pattern) : d2280 (change p 224 none) = d92 p := by
  change (if p 161 then d2279 (change p 224 none) else d2278 (change p 224 none)) = d92 p
  rw [sub10175, sub10174]
  rfl
theorem sub10177 (p : Pattern) : d2281 (change p 224 none) = d93 p := by
  change (if p 161 then d12 (change p 224 none) else d2279 (change p 224 none)) = d93 p
  rw [sub10059, sub10175]
  rfl
theorem sub10178 (p : Pattern) : d2282 (change p 224 none) = d94 p := by
  change (if p 160 then d2281 (change p 224 none) else d2280 (change p 224 none)) = d94 p
  rw [sub10177, sub10176]
  rfl
theorem sub10179 (p : Pattern) : d2283 (change p 224 none) = d95 p := by
  change (if p 160 then d12 (change p 224 none) else d2281 (change p 224 none)) = d95 p
  rw [sub10059, sub10177]
  rfl
theorem sub10180 (p : Pattern) : d2284 (change p 224 none) = d96 p := by
  change (if p 141 then d2283 (change p 224 none) else d2282 (change p 224 none)) = d96 p
  rw [sub10179, sub10178]
  rfl
theorem sub10181 (p : Pattern) : d2285 (change p 224 none) = d97 p := by
  change (if p 138 then d2284 (change p 224 none) else d2276 (change p 224 none)) = d97 p
  rw [sub10180, sub10172]
  rfl
theorem sub10182 (p : Pattern) : d2286 (change p 224 none) = d98 p := by
  change (if p 116 then d2285 (change p 224 none) else d2271 (change p 224 none)) = d98 p
  rw [sub10181, sub10167]
  rfl
theorem sub10183 (p : Pattern) : d2287 (change p 224 none) = d16 p := by
  change (if p 163 then d2201 (change p 224 none) else d2191 (change p 224 none)) = d16 p
  rw [sub10082, sub10069]
  simp only [ite_self]
theorem sub10184 (p : Pattern) : d2288 (change p 224 none) = d22 p := by
  change (if p 162 then d2202 (change p 224 none) else d2287 (change p 224 none)) = d22 p
  rw [sub10083, sub10183]
  rfl
theorem sub10185 (p : Pattern) : d2289 (change p 224 none) = d29 p := by
  change (if p 161 then d2207 (change p 224 none) else d2288 (change p 224 none)) = d29 p
  rw [sub10091, sub10184]
  rfl
theorem sub10186 (p : Pattern) : d2290 (change p 224 none) = d52 p := by
  change (if p 160 then d2227 (change p 224 none) else d2289 (change p 224 none)) = d52 p
  rw [sub10120, sub10185]
  rfl
theorem sub10187 (p : Pattern) : d2291 (change p 224 none) = d76 p := by
  change (if p 160 then d2253 (change p 224 none) else d2265 (change p 224 none)) = d76 p
  rw [sub10149, sub10161]
  rfl
theorem sub10188 (p : Pattern) : d2292 (change p 224 none) = d77 p := by
  change (if p 141 then d2291 (change p 224 none) else d2290 (change p 224 none)) = d77 p
  rw [sub10187, sub10186]
  rfl
theorem sub10189 (p : Pattern) : d2293 (change p 224 none) = d88 p := by
  change (if p 138 then d2270 (change p 224 none) else d2292 (change p 224 none)) = d88 p
  rw [sub10166, sub10188]
  rfl
theorem sub10190 (p : Pattern) : d2294 (change p 224 none) = d99 p := by
  change (if p 138 then d12 (change p 224 none) else d2270 (change p 224 none)) = d99 p
  rw [sub10059, sub10166]
  rfl
theorem sub10191 (p : Pattern) : d2295 (change p 224 none) = d100 p := by
  change (if p 116 then d2294 (change p 224 none) else d2293 (change p 224 none)) = d100 p
  rw [sub10190, sub10189]
  rfl
theorem sub10192 (p : Pattern) : d2296 (change p 224 none) = d101 p := by
  change (if p 115 then d2295 (change p 224 none) else d2286 (change p 224 none)) = d101 p
  rw [sub10191, sub10182]
  rfl
theorem sub10193 (p : Pattern) : d2297 (change p 224 none) = d14 p := by
  change d14 (change p 224 none) = d14 p
  exact sub10061 p
theorem sub10194 (p : Pattern) : d2298 (change p 224 none) = d14 p := by
  change (if p 204 then d2185 (change p 224 none) else d2297 (change p 224 none)) = d14 p
  rw [sub10063, sub10193]
  simp only [ite_self]
theorem sub10195 (p : Pattern) : d2299 (change p 224 none) = d16 p := by
  change (if p 182 then d2187 (change p 224 none) else d2298 (change p 224 none)) = d16 p
  rw [sub10065, sub10194]
  rfl
theorem sub10196 (p : Pattern) : d2300 (change p 224 none) = d16 p := by
  change (if p 163 then d2195 (change p 224 none) else d2299 (change p 224 none)) = d16 p
  rw [sub10073, sub10195]
  simp only [ite_self]
theorem sub10197 (p : Pattern) : d2301 (change p 224 none) = d22 p := by
  change (if p 162 then d2202 (change p 224 none) else d2300 (change p 224 none)) = d22 p
  rw [sub10083, sub10196]
  rfl
theorem sub10198 (p : Pattern) : d2302 (change p 224 none) = d29 p := by
  change (if p 161 then d2207 (change p 224 none) else d2301 (change p 224 none)) = d29 p
  rw [sub10091, sub10197]
  rfl
theorem sub10199 (p : Pattern) : d2303 (change p 224 none) = d52 p := by
  change (if p 160 then d2227 (change p 224 none) else d2302 (change p 224 none)) = d52 p
  rw [sub10120, sub10198]
  rfl
end NetHack.Sokoban22Refined85
