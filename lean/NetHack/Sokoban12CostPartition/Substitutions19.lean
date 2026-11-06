/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions18
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2280 (p : Pattern) : d54 (change p 10000 (some 158)) = d54 p := by
  change (if p 193 then d4 (change p 10000 (some 158)) else d2 (change p 10000 (some 158))) = d54 p
  rw [sub2279, sub2276]
  rfl
theorem sub2281 (p : Pattern) : d55 (change p 10000 (some 158)) = d55 p := by
  change (if p 192 then d54 (change p 10000 (some 158)) else d2 (change p 10000 (some 158))) = d55 p
  rw [sub2280, sub2276]
  rfl
theorem sub2282 (p : Pattern) : d56 (change p 10000 (some 158)) = d56 p := by
  change (if p 186 then d55 (change p 10000 (some 158)) else d7 (change p 10000 (some 158))) = d56 p
  rw [sub2281, sub2278]
  rfl
theorem sub2283 (p : Pattern) : d57 (change p 10000 (some 158)) = d57 p := by
  change (if p 160 then d56 (change p 10000 (some 158)) else d7 (change p 10000 (some 158))) = d57 p
  rw [sub2282, sub2278]
  rfl
theorem sub2284 (p : Pattern) : d1 (change p 10000 (some 158)) = d1 p := by
  rfl
theorem sub2285 (p : Pattern) : d8 (change p 10000 (some 158)) = d8 p := by
  change (if p 271 then d1 (change p 10000 (some 158)) else d0 (change p 10000 (some 158))) = d8 p
  rw [sub2284, sub2275]
  rfl
theorem sub2286 (p : Pattern) : d3 (change p 10000 (some 158)) = d3 p := by
  rfl
theorem sub2287 (p : Pattern) : d9 (change p 10000 (some 158)) = d9 p := by
  change (if p 271 then d3 (change p 10000 (some 158)) else d2 (change p 10000 (some 158))) = d9 p
  rw [sub2286, sub2276]
  rfl
theorem sub2288 (p : Pattern) : d10 (change p 10000 (some 158)) = d10 p := by
  change (if p 193 then d9 (change p 10000 (some 158)) else d8 (change p 10000 (some 158))) = d10 p
  rw [sub2287, sub2285]
  rfl
theorem sub2289 (p : Pattern) : d11 (change p 10000 (some 158)) = d11 p := by
  change (if p 192 then d10 (change p 10000 (some 158)) else d8 (change p 10000 (some 158))) = d11 p
  rw [sub2288, sub2285]
  rfl
theorem sub2290 (p : Pattern) : d12 (change p 10000 (some 158)) = d12 p := by
  change (if p 168 then d11 (change p 10000 (some 158)) else d7 (change p 10000 (some 158))) = d12 p
  rw [sub2289, sub2278]
  rfl
theorem sub2291 (p : Pattern) : d5 (change p 10000 (some 158)) = d5 p := by
  rfl
theorem sub2292 (p : Pattern) : d58 (change p 10000 (some 158)) = d58 p := by
  change (if p 271 then d5 (change p 10000 (some 158)) else d4 (change p 10000 (some 158))) = d58 p
  rw [sub2291, sub2279]
  rfl
theorem sub2293 (p : Pattern) : d59 (change p 10000 (some 158)) = d59 p := by
  change (if p 193 then d58 (change p 10000 (some 158)) else d9 (change p 10000 (some 158))) = d59 p
  rw [sub2292, sub2287]
  rfl
theorem sub2294 (p : Pattern) : d60 (change p 10000 (some 158)) = d60 p := by
  change (if p 192 then d59 (change p 10000 (some 158)) else d9 (change p 10000 (some 158))) = d60 p
  rw [sub2293, sub2287]
  rfl
theorem sub2295 (p : Pattern) : d61 (change p 10000 (some 158)) = d61 p := by
  change (if p 186 then d60 (change p 10000 (some 158)) else d11 (change p 10000 (some 158))) = d61 p
  rw [sub2294, sub2289]
  rfl
theorem sub2296 (p : Pattern) : d62 (change p 10000 (some 158)) = d62 p := by
  change (if p 168 then d61 (change p 10000 (some 158)) else d56 (change p 10000 (some 158))) = d62 p
  rw [sub2295, sub2282]
  rfl
theorem sub2297 (p : Pattern) : d63 (change p 10000 (some 158)) = d63 p := by
  change (if p 160 then d62 (change p 10000 (some 158)) else d12 (change p 10000 (some 158))) = d63 p
  rw [sub2296, sub2290]
  rfl
theorem sub2298 (p : Pattern) : d64 (change p 10000 (some 158)) = d64 p := by
  change (if p 141 then d63 (change p 10000 (some 158)) else d57 (change p 10000 (some 158))) = d64 p
  rw [sub2297, sub2283]
  rfl
theorem sub2299 (p : Pattern) : d106 (change p 10000 (some 158)) = d106 p := by
  change (if p 160 then d55 (change p 10000 (some 158)) else d7 (change p 10000 (some 158))) = d106 p
  rw [sub2281, sub2278]
  rfl
theorem sub2300 (p : Pattern) : d119 (change p 10000 (some 158)) = d119 p := by
  change (if p 187 then d55 (change p 10000 (some 158)) else d7 (change p 10000 (some 158))) = d119 p
  rw [sub2281, sub2278]
  rfl
theorem sub2301 (p : Pattern) : d120 (change p 10000 (some 158)) = d120 p := by
  change (if p 186 then d119 (change p 10000 (some 158)) else d7 (change p 10000 (some 158))) = d120 p
  rw [sub2300, sub2278]
  rfl
theorem sub2302 (p : Pattern) : d121 (change p 10000 (some 158)) = d121 p := by
  change (if p 160 then d55 (change p 10000 (some 158)) else d120 (change p 10000 (some 158))) = d121 p
  rw [sub2281, sub2301]
  rfl
theorem sub2303 (p : Pattern) : d122 (change p 10000 (some 158)) = d122 p := by
  change (if p 159 then d121 (change p 10000 (some 158)) else d106 (change p 10000 (some 158))) = d122 p
  rw [sub2302, sub2299]
  rfl
theorem sub2304 (p : Pattern) : d179 (change p 10000 (some 158)) = d122 p := by
  change d122 (change p 10000 (some 158)) = d122 p
  exact sub2303 p
theorem sub2305 (p : Pattern) : d65 (change p 10000 (some 158)) = d65 p := by
  change (if p 168 then d60 (change p 10000 (some 158)) else d55 (change p 10000 (some 158))) = d65 p
  rw [sub2294, sub2281]
  rfl
theorem sub2306 (p : Pattern) : d109 (change p 10000 (some 158)) = d109 p := by
  change (if p 160 then d65 (change p 10000 (some 158)) else d12 (change p 10000 (some 158))) = d109 p
  rw [sub2305, sub2290]
  rfl
theorem sub2307 (p : Pattern) : d125 (change p 10000 (some 158)) = d125 p := by
  change (if p 187 then d60 (change p 10000 (some 158)) else d11 (change p 10000 (some 158))) = d125 p
  rw [sub2294, sub2289]
  rfl
theorem sub2308 (p : Pattern) : d126 (change p 10000 (some 158)) = d126 p := by
  change (if p 186 then d125 (change p 10000 (some 158)) else d11 (change p 10000 (some 158))) = d126 p
  rw [sub2307, sub2289]
  rfl
theorem sub2309 (p : Pattern) : d127 (change p 10000 (some 158)) = d127 p := by
  change (if p 168 then d126 (change p 10000 (some 158)) else d120 (change p 10000 (some 158))) = d127 p
  rw [sub2308, sub2301]
  rfl
theorem sub2310 (p : Pattern) : d128 (change p 10000 (some 158)) = d128 p := by
  change (if p 160 then d65 (change p 10000 (some 158)) else d127 (change p 10000 (some 158))) = d128 p
  rw [sub2305, sub2309]
  rfl
theorem sub2311 (p : Pattern) : d129 (change p 10000 (some 158)) = d129 p := by
  change (if p 159 then d128 (change p 10000 (some 158)) else d109 (change p 10000 (some 158))) = d129 p
  rw [sub2310, sub2306]
  rfl
theorem sub2312 (p : Pattern) : d237 (change p 10000 (some 158)) = d129 p := by
  change d129 (change p 10000 (some 158)) = d129 p
  exact sub2311 p
theorem sub2313 (p : Pattern) : d238 (change p 10000 (some 158)) = d775 p := by
  change (if p 141 then d237 (change p 10000 (some 158)) else d179 (change p 10000 (some 158))) = d775 p
  rw [sub2312, sub2304]
  rfl
theorem sub2314 (p : Pattern) : d239 (change p 10000 (some 158)) = d776 p := by
  change (if p 134 then d238 (change p 10000 (some 158)) else d64 (change p 10000 (some 158))) = d776 p
  rw [sub2313, sub2298]
  rfl
theorem sub2315 (p : Pattern) : d68 (change p 10000 (some 158)) = d55 p := by
  change d55 (change p 10000 (some 158)) = d55 p
  exact sub2281 p
theorem sub2316 (p : Pattern) : d69 (change p 10000 (some 158)) = d65 p := by
  change d65 (change p 10000 (some 158)) = d65 p
  exact sub2305 p
theorem sub2317 (p : Pattern) : d70 (change p 10000 (some 158)) = d66 p := by
  change (if p 141 then d69 (change p 10000 (some 158)) else d68 (change p 10000 (some 158))) = d66 p
  rw [sub2316, sub2315]
  rfl
theorem sub2318 (p : Pattern) : d181 (change p 10000 (some 158)) = d55 p := by
  change d55 (change p 10000 (some 158)) = d55 p
  exact sub2281 p
theorem sub2319 (p : Pattern) : d240 (change p 10000 (some 158)) = d65 p := by
  change d65 (change p 10000 (some 158)) = d65 p
  exact sub2305 p
theorem sub2320 (p : Pattern) : d241 (change p 10000 (some 158)) = d66 p := by
  change (if p 141 then d240 (change p 10000 (some 158)) else d181 (change p 10000 (some 158))) = d66 p
  rw [sub2319, sub2318]
  rfl
theorem sub2321 (p : Pattern) : d242 (change p 10000 (some 158)) = d66 p := by
  change (if p 134 then d241 (change p 10000 (some 158)) else d70 (change p 10000 (some 158))) = d66 p
  rw [sub2320, sub2317]
  simp only [ite_self]
theorem sub2322 (p : Pattern) : d243 (change p 10000 (some 158)) = d778 p := by
  change (if p 133 then d242 (change p 10000 (some 158)) else d239 (change p 10000 (some 158))) = d778 p
  rw [sub2321, sub2314]
  rfl
theorem sub2323 (p : Pattern) : d66 (change p 10000 (some 158)) = d66 p := by
  change (if p 141 then d65 (change p 10000 (some 158)) else d55 (change p 10000 (some 158))) = d66 p
  rw [sub2305, sub2281]
  rfl
theorem sub2324 (p : Pattern) : d244 (change p 10000 (some 158)) = d66 p := by
  change (if p 133 then d66 (change p 10000 (some 158)) else d242 (change p 10000 (some 158))) = d66 p
  rw [sub2323, sub2321]
  simp only [ite_self]
theorem sub2325 (p : Pattern) : d245 (change p 10000 (some 158)) = d1189 p := by
  change (if p 132 then d244 (change p 10000 (some 158)) else d243 (change p 10000 (some 158))) = d1189 p
  rw [sub2324, sub2322]
  rfl
theorem sub2326 (p : Pattern) : d137 (change p 10000 (some 158)) = d137 p := by
  change (if p 186 then d55 (change p 10000 (some 158)) else d119 (change p 10000 (some 158))) = d137 p
  rw [sub2281, sub2300]
  rfl
theorem sub2327 (p : Pattern) : d139 (change p 10000 (some 158)) = d139 p := by
  change (if p 160 then d137 (change p 10000 (some 158)) else d120 (change p 10000 (some 158))) = d139 p
  rw [sub2326, sub2301]
  rfl
theorem sub2328 (p : Pattern) : d153 (change p 10000 (some 158)) = d153 p := by
  change (if p 159 then d139 (change p 10000 (some 158)) else d57 (change p 10000 (some 158))) = d153 p
  rw [sub2327, sub2283]
  rfl
theorem sub2329 (p : Pattern) : d186 (change p 10000 (some 158)) = d153 p := by
  change d153 (change p 10000 (some 158)) = d153 p
  exact sub2328 p
theorem sub2330 (p : Pattern) : d143 (change p 10000 (some 158)) = d143 p := by
  change (if p 186 then d60 (change p 10000 (some 158)) else d125 (change p 10000 (some 158))) = d143 p
  rw [sub2294, sub2307]
  rfl
theorem sub2331 (p : Pattern) : d144 (change p 10000 (some 158)) = d144 p := by
  change (if p 168 then d143 (change p 10000 (some 158)) else d137 (change p 10000 (some 158))) = d144 p
  rw [sub2330, sub2326]
  rfl
theorem sub2332 (p : Pattern) : d146 (change p 10000 (some 158)) = d146 p := by
  change (if p 160 then d144 (change p 10000 (some 158)) else d127 (change p 10000 (some 158))) = d146 p
  rw [sub2331, sub2309]
  rfl
theorem sub2333 (p : Pattern) : d155 (change p 10000 (some 158)) = d155 p := by
  change (if p 159 then d146 (change p 10000 (some 158)) else d63 (change p 10000 (some 158))) = d155 p
  rw [sub2332, sub2297]
  rfl
theorem sub2334 (p : Pattern) : d246 (change p 10000 (some 158)) = d155 p := by
  change d155 (change p 10000 (some 158)) = d155 p
  exact sub2333 p
theorem sub2335 (p : Pattern) : d247 (change p 10000 (some 158)) = d783 p := by
  change (if p 141 then d246 (change p 10000 (some 158)) else d186 (change p 10000 (some 158))) = d783 p
  rw [sub2334, sub2329]
  rfl
theorem sub2336 (p : Pattern) : d248 (change p 10000 (some 158)) = d784 p := by
  change (if p 134 then d66 (change p 10000 (some 158)) else d247 (change p 10000 (some 158))) = d784 p
  rw [sub2323, sub2335]
  rfl
theorem sub2337 (p : Pattern) : d188 (change p 10000 (some 158)) = d55 p := by
  change d55 (change p 10000 (some 158)) = d55 p
  exact sub2281 p
theorem sub2338 (p : Pattern) : d249 (change p 10000 (some 158)) = d65 p := by
  change d65 (change p 10000 (some 158)) = d65 p
  exact sub2305 p
theorem sub2339 (p : Pattern) : d250 (change p 10000 (some 158)) = d66 p := by
  change (if p 141 then d249 (change p 10000 (some 158)) else d188 (change p 10000 (some 158))) = d66 p
  rw [sub2338, sub2337]
  rfl
theorem sub2340 (p : Pattern) : d251 (change p 10000 (some 158)) = d66 p := by
  change (if p 134 then d66 (change p 10000 (some 158)) else d250 (change p 10000 (some 158))) = d66 p
  rw [sub2323, sub2339]
  simp only [ite_self]
theorem sub2341 (p : Pattern) : d252 (change p 10000 (some 158)) = d785 p := by
  change (if p 133 then d251 (change p 10000 (some 158)) else d248 (change p 10000 (some 158))) = d785 p
  rw [sub2340, sub2336]
  rfl
theorem sub2342 (p : Pattern) : d191 (change p 10000 (some 158)) = d55 p := by
  change d55 (change p 10000 (some 158)) = d55 p
  exact sub2281 p
theorem sub2343 (p : Pattern) : d253 (change p 10000 (some 158)) = d65 p := by
  change d65 (change p 10000 (some 158)) = d65 p
  exact sub2305 p
theorem sub2344 (p : Pattern) : d254 (change p 10000 (some 158)) = d66 p := by
  change (if p 141 then d253 (change p 10000 (some 158)) else d191 (change p 10000 (some 158))) = d66 p
  rw [sub2343, sub2342]
  rfl
theorem sub2345 (p : Pattern) : d255 (change p 10000 (some 158)) = d66 p := by
  change (if p 134 then d66 (change p 10000 (some 158)) else d254 (change p 10000 (some 158))) = d66 p
  rw [sub2323, sub2344]
  simp only [ite_self]
theorem sub2346 (p : Pattern) : d256 (change p 10000 (some 158)) = d66 p := by
  change (if p 133 then d66 (change p 10000 (some 158)) else d255 (change p 10000 (some 158))) = d66 p
  rw [sub2323, sub2345]
  simp only [ite_self]
theorem sub2347 (p : Pattern) : d257 (change p 10000 (some 158)) = d1190 p := by
  change (if p 132 then d256 (change p 10000 (some 158)) else d252 (change p 10000 (some 158))) = d1190 p
  rw [sub2346, sub2341]
  rfl
theorem sub2348 (p : Pattern) : d258 (change p 10000 (some 158)) = d1191 p := by
  change (if p 108 then d257 (change p 10000 (some 158)) else d245 (change p 10000 (some 158))) = d1191 p
  rw [sub2347, sub2325]
  rfl
theorem sub2349 (p : Pattern) : d0 (change p 10000 (some 159)) = d0 p := by
  rfl
theorem sub2350 (p : Pattern) : d2 (change p 10000 (some 159)) = d2 p := by
  rfl
theorem sub2351 (p : Pattern) : d6 (change p 10000 (some 159)) = d6 p := by
  change (if p 193 then d2 (change p 10000 (some 159)) else d0 (change p 10000 (some 159))) = d6 p
  rw [sub2350, sub2349]
  rfl
theorem sub2352 (p : Pattern) : d7 (change p 10000 (some 159)) = d7 p := by
  change (if p 192 then d6 (change p 10000 (some 159)) else d0 (change p 10000 (some 159))) = d7 p
  rw [sub2351, sub2349]
  rfl
theorem sub2353 (p : Pattern) : d4 (change p 10000 (some 159)) = d4 p := by
  rfl
theorem sub2354 (p : Pattern) : d54 (change p 10000 (some 159)) = d54 p := by
  change (if p 193 then d4 (change p 10000 (some 159)) else d2 (change p 10000 (some 159))) = d54 p
  rw [sub2353, sub2350]
  rfl
theorem sub2355 (p : Pattern) : d55 (change p 10000 (some 159)) = d55 p := by
  change (if p 192 then d54 (change p 10000 (some 159)) else d2 (change p 10000 (some 159))) = d55 p
  rw [sub2354, sub2350]
  rfl
theorem sub2356 (p : Pattern) : d56 (change p 10000 (some 159)) = d56 p := by
  change (if p 186 then d55 (change p 10000 (some 159)) else d7 (change p 10000 (some 159))) = d56 p
  rw [sub2355, sub2352]
  rfl
theorem sub2357 (p : Pattern) : d57 (change p 10000 (some 159)) = d57 p := by
  change (if p 160 then d56 (change p 10000 (some 159)) else d7 (change p 10000 (some 159))) = d57 p
  rw [sub2356, sub2352]
  rfl
theorem sub2358 (p : Pattern) : d1 (change p 10000 (some 159)) = d1 p := by
  rfl
theorem sub2359 (p : Pattern) : d8 (change p 10000 (some 159)) = d8 p := by
  change (if p 271 then d1 (change p 10000 (some 159)) else d0 (change p 10000 (some 159))) = d8 p
  rw [sub2358, sub2349]
  rfl
theorem sub2360 (p : Pattern) : d3 (change p 10000 (some 159)) = d3 p := by
  rfl
theorem sub2361 (p : Pattern) : d9 (change p 10000 (some 159)) = d9 p := by
  change (if p 271 then d3 (change p 10000 (some 159)) else d2 (change p 10000 (some 159))) = d9 p
  rw [sub2360, sub2350]
  rfl
theorem sub2362 (p : Pattern) : d10 (change p 10000 (some 159)) = d10 p := by
  change (if p 193 then d9 (change p 10000 (some 159)) else d8 (change p 10000 (some 159))) = d10 p
  rw [sub2361, sub2359]
  rfl
theorem sub2363 (p : Pattern) : d11 (change p 10000 (some 159)) = d11 p := by
  change (if p 192 then d10 (change p 10000 (some 159)) else d8 (change p 10000 (some 159))) = d11 p
  rw [sub2362, sub2359]
  rfl
theorem sub2364 (p : Pattern) : d12 (change p 10000 (some 159)) = d12 p := by
  change (if p 168 then d11 (change p 10000 (some 159)) else d7 (change p 10000 (some 159))) = d12 p
  rw [sub2363, sub2352]
  rfl
theorem sub2365 (p : Pattern) : d5 (change p 10000 (some 159)) = d5 p := by
  rfl
theorem sub2366 (p : Pattern) : d58 (change p 10000 (some 159)) = d58 p := by
  change (if p 271 then d5 (change p 10000 (some 159)) else d4 (change p 10000 (some 159))) = d58 p
  rw [sub2365, sub2353]
  rfl
theorem sub2367 (p : Pattern) : d59 (change p 10000 (some 159)) = d59 p := by
  change (if p 193 then d58 (change p 10000 (some 159)) else d9 (change p 10000 (some 159))) = d59 p
  rw [sub2366, sub2361]
  rfl
theorem sub2368 (p : Pattern) : d60 (change p 10000 (some 159)) = d60 p := by
  change (if p 192 then d59 (change p 10000 (some 159)) else d9 (change p 10000 (some 159))) = d60 p
  rw [sub2367, sub2361]
  rfl
theorem sub2369 (p : Pattern) : d61 (change p 10000 (some 159)) = d61 p := by
  change (if p 186 then d60 (change p 10000 (some 159)) else d11 (change p 10000 (some 159))) = d61 p
  rw [sub2368, sub2363]
  rfl
theorem sub2370 (p : Pattern) : d62 (change p 10000 (some 159)) = d62 p := by
  change (if p 168 then d61 (change p 10000 (some 159)) else d56 (change p 10000 (some 159))) = d62 p
  rw [sub2369, sub2356]
  rfl
theorem sub2371 (p : Pattern) : d63 (change p 10000 (some 159)) = d63 p := by
  change (if p 160 then d62 (change p 10000 (some 159)) else d12 (change p 10000 (some 159))) = d63 p
  rw [sub2370, sub2364]
  rfl
theorem sub2372 (p : Pattern) : d64 (change p 10000 (some 159)) = d64 p := by
  change (if p 141 then d63 (change p 10000 (some 159)) else d57 (change p 10000 (some 159))) = d64 p
  rw [sub2371, sub2357]
  rfl
theorem sub2373 (p : Pattern) : d106 (change p 10000 (some 159)) = d106 p := by
  change (if p 160 then d55 (change p 10000 (some 159)) else d7 (change p 10000 (some 159))) = d106 p
  rw [sub2355, sub2352]
  rfl
theorem sub2374 (p : Pattern) : d119 (change p 10000 (some 159)) = d119 p := by
  change (if p 187 then d55 (change p 10000 (some 159)) else d7 (change p 10000 (some 159))) = d119 p
  rw [sub2355, sub2352]
  rfl
theorem sub2375 (p : Pattern) : d120 (change p 10000 (some 159)) = d120 p := by
  change (if p 186 then d119 (change p 10000 (some 159)) else d7 (change p 10000 (some 159))) = d120 p
  rw [sub2374, sub2352]
  rfl
theorem sub2376 (p : Pattern) : d121 (change p 10000 (some 159)) = d121 p := by
  change (if p 160 then d55 (change p 10000 (some 159)) else d120 (change p 10000 (some 159))) = d121 p
  rw [sub2355, sub2375]
  rfl
theorem sub2377 (p : Pattern) : d122 (change p 10000 (some 159)) = d121 p := by
  change d121 (change p 10000 (some 159)) = d121 p
  exact sub2376 p
theorem sub2378 (p : Pattern) : d179 (change p 10000 (some 159)) = d1192 p := by
  change (if p 158 then d122 (change p 10000 (some 159)) else d106 (change p 10000 (some 159))) = d1192 p
  rw [sub2377, sub2373]
  rfl
theorem sub2379 (p : Pattern) : d65 (change p 10000 (some 159)) = d65 p := by
  change (if p 168 then d60 (change p 10000 (some 159)) else d55 (change p 10000 (some 159))) = d65 p
  rw [sub2368, sub2355]
  rfl
theorem sub2380 (p : Pattern) : d109 (change p 10000 (some 159)) = d109 p := by
  change (if p 160 then d65 (change p 10000 (some 159)) else d12 (change p 10000 (some 159))) = d109 p
  rw [sub2379, sub2364]
  rfl
theorem sub2381 (p : Pattern) : d125 (change p 10000 (some 159)) = d125 p := by
  change (if p 187 then d60 (change p 10000 (some 159)) else d11 (change p 10000 (some 159))) = d125 p
  rw [sub2368, sub2363]
  rfl
theorem sub2382 (p : Pattern) : d126 (change p 10000 (some 159)) = d126 p := by
  change (if p 186 then d125 (change p 10000 (some 159)) else d11 (change p 10000 (some 159))) = d126 p
  rw [sub2381, sub2363]
  rfl
theorem sub2383 (p : Pattern) : d127 (change p 10000 (some 159)) = d127 p := by
  change (if p 168 then d126 (change p 10000 (some 159)) else d120 (change p 10000 (some 159))) = d127 p
  rw [sub2382, sub2375]
  rfl
theorem sub2384 (p : Pattern) : d128 (change p 10000 (some 159)) = d128 p := by
  change (if p 160 then d65 (change p 10000 (some 159)) else d127 (change p 10000 (some 159))) = d128 p
  rw [sub2379, sub2383]
  rfl
theorem sub2385 (p : Pattern) : d129 (change p 10000 (some 159)) = d128 p := by
  change d128 (change p 10000 (some 159)) = d128 p
  exact sub2384 p
theorem sub2386 (p : Pattern) : d237 (change p 10000 (some 159)) = d1193 p := by
  change (if p 158 then d129 (change p 10000 (some 159)) else d109 (change p 10000 (some 159))) = d1193 p
  rw [sub2385, sub2380]
  rfl
theorem sub2387 (p : Pattern) : d238 (change p 10000 (some 159)) = d1194 p := by
  change (if p 141 then d237 (change p 10000 (some 159)) else d179 (change p 10000 (some 159))) = d1194 p
  rw [sub2386, sub2378]
  rfl
theorem sub2388 (p : Pattern) : d239 (change p 10000 (some 159)) = d1195 p := by
  change (if p 134 then d238 (change p 10000 (some 159)) else d64 (change p 10000 (some 159))) = d1195 p
  rw [sub2387, sub2372]
  rfl
theorem sub2389 (p : Pattern) : d68 (change p 10000 (some 159)) = d68 p := by
  change (if p 158 then d55 (change p 10000 (some 159)) else d57 (change p 10000 (some 159))) = d68 p
  rw [sub2355, sub2357]
  rfl
theorem sub2390 (p : Pattern) : d69 (change p 10000 (some 159)) = d69 p := by
  change (if p 158 then d65 (change p 10000 (some 159)) else d63 (change p 10000 (some 159))) = d69 p
  rw [sub2379, sub2371]
  rfl
theorem sub2391 (p : Pattern) : d70 (change p 10000 (some 159)) = d70 p := by
  change (if p 141 then d69 (change p 10000 (some 159)) else d68 (change p 10000 (some 159))) = d70 p
  rw [sub2390, sub2389]
  rfl
theorem sub2392 (p : Pattern) : d181 (change p 10000 (some 159)) = d1196 p := by
  change (if p 158 then d55 (change p 10000 (some 159)) else d122 (change p 10000 (some 159))) = d1196 p
  rw [sub2355, sub2377]
  rfl
theorem sub2393 (p : Pattern) : d240 (change p 10000 (some 159)) = d1197 p := by
  change (if p 158 then d65 (change p 10000 (some 159)) else d129 (change p 10000 (some 159))) = d1197 p
  rw [sub2379, sub2385]
  rfl
theorem sub2394 (p : Pattern) : d241 (change p 10000 (some 159)) = d1198 p := by
  change (if p 141 then d240 (change p 10000 (some 159)) else d181 (change p 10000 (some 159))) = d1198 p
  rw [sub2393, sub2392]
  rfl
theorem sub2395 (p : Pattern) : d242 (change p 10000 (some 159)) = d1199 p := by
  change (if p 134 then d241 (change p 10000 (some 159)) else d70 (change p 10000 (some 159))) = d1199 p
  rw [sub2394, sub2391]
  rfl
theorem sub2396 (p : Pattern) : d243 (change p 10000 (some 159)) = d1200 p := by
  change (if p 133 then d242 (change p 10000 (some 159)) else d239 (change p 10000 (some 159))) = d1200 p
  rw [sub2395, sub2388]
  rfl
theorem sub2397 (p : Pattern) : d66 (change p 10000 (some 159)) = d66 p := by
  change (if p 141 then d65 (change p 10000 (some 159)) else d55 (change p 10000 (some 159))) = d66 p
  rw [sub2379, sub2355]
  rfl
theorem sub2398 (p : Pattern) : d244 (change p 10000 (some 159)) = d1201 p := by
  change (if p 133 then d66 (change p 10000 (some 159)) else d242 (change p 10000 (some 159))) = d1201 p
  rw [sub2397, sub2395]
  rfl
theorem sub2399 (p : Pattern) : d245 (change p 10000 (some 159)) = d1202 p := by
  change (if p 132 then d244 (change p 10000 (some 159)) else d243 (change p 10000 (some 159))) = d1202 p
  rw [sub2398, sub2396]
  rfl
end NetHack.Sokoban12CostPartition
