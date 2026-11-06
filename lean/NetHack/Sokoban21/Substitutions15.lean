/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions14
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s2250 (pattern : Twelve) : d1302 (change pattern 2 12) = d1302 pattern := by
  change (if pattern.f then d6 (change pattern 2 12) else d1290 (change pattern 2 12)) = d1302 pattern
  rw [s2188, s2249]
  rfl
theorem s2251 (pattern : Twelve) : d1310 (change pattern 2 12) = d1310 pattern := by
  change (if pattern.e then d1302 (change pattern 2 12) else d1295 (change pattern 2 12)) = d1310 pattern
  rw [s2250, s2238]
  rfl
theorem s2252 (pattern : Twelve) : d1316 (change pattern 2 12) = d1316 pattern := by
  change (if pattern.j then d1310 (change pattern 2 12) else d1309 (change pattern 2 12)) = d1316 pattern
  rw [s2251, s2247]
  rfl
theorem s2253 (pattern : Twelve) : d1429 (change pattern 2 12) = d1316 pattern := by
  change d1316 (change pattern 2 12) = d1316 pattern
  exact s2252 pattern
theorem s2254 (pattern : Twelve) : d1431 (change pattern 2 12) = d2269 pattern := by
  change (if pattern.g then d1429 (change pattern 2 12) else d1428 (change pattern 2 12)) = d2269 pattern
  rw [s2253, s2244]
  rfl
theorem s2255 (pattern : Twelve) : d1430 (change pattern 2 12) = d1313 pattern := by
  change d1313 (change pattern 2 12) = d1313 pattern
  exact s2243 pattern
theorem s2256 (pattern : Twelve) : d1432 (change pattern 2 12) = d2269 pattern := by
  change (if pattern.g then d1429 (change pattern 2 12) else d1430 (change pattern 2 12)) = d2269 pattern
  rw [s2253, s2255]
  rfl
theorem s2257 (pattern : Twelve) : d1433 (change pattern 2 12) = d2269 pattern := by
  change (if pattern.b then d1432 (change pattern 2 12) else d1431 (change pattern 2 12)) = d2269 pattern
  rw [s2256, s2254]
  simp only [ite_self]
theorem s2258 (pattern : Twelve) : d1434 (change pattern 2 12) = d2269 pattern := by
  change (if pattern.a then d1432 (change pattern 2 12) else d1433 (change pattern 2 12)) = d2269 pattern
  rw [s2256, s2257]
  simp only [ite_self]
theorem s2259 (pattern : Twelve) : d1324 (change pattern 2 12) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 2 12) else d11 (change pattern 2 12)) = d1324 pattern
  rw [s2183, s2180]
  rfl
theorem s2260 (pattern : Twelve) : d1649 (change pattern 2 12) = d1649 pattern := by
  change (if pattern.f then d1324 (change pattern 2 12) else d19 (change pattern 2 12)) = d1649 pattern
  rw [s2259, s2181]
  rfl
theorem s2261 (pattern : Twelve) : d1650 (change pattern 2 12) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 2 12) else d25 (change pattern 2 12)) = d1650 pattern
  rw [s2188, s2186]
  rfl
theorem s2262 (pattern : Twelve) : d1656 (change pattern 2 12) = d1656 pattern := by
  change (if pattern.e then d1650 (change pattern 2 12) else d1649 (change pattern 2 12)) = d1656 pattern
  rw [s2261, s2260]
  rfl
theorem s2263 (pattern : Twelve) : d13 (change pattern 2 12) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 2 12) else d4 (change pattern 2 12)) = d13 pattern
  rw [s2188, s2182]
  rfl
theorem s2264 (pattern : Twelve) : d20 (change pattern 2 12) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 2 12) else d12 (change pattern 2 12)) = d20 pattern
  rw [s2263, s2185]
  rfl
theorem s2265 (pattern : Twelve) : d1644 (change pattern 2 12) = d1644 pattern := by
  change (if pattern.i then d20 (change pattern 2 12) else d1324 (change pattern 2 12)) = d1644 pattern
  rw [s2264, s2259]
  rfl
theorem s2266 (pattern : Twelve) : d1645 (change pattern 2 12) = d1645 pattern := by
  change (if pattern.i then d6 (change pattern 2 12) else d1324 (change pattern 2 12)) = d1645 pattern
  rw [s2188, s2259]
  rfl
theorem s2267 (pattern : Twelve) : d1647 (change pattern 2 12) = d1647 pattern := by
  change (if pattern.h then d1645 (change pattern 2 12) else d1644 (change pattern 2 12)) = d1647 pattern
  rw [s2266, s2265]
  rfl
theorem s2268 (pattern : Twelve) : d1651 (change pattern 2 12) = d1651 pattern := by
  change (if pattern.f then d1647 (change pattern 2 12) else d1286 (change pattern 2 12)) = d1651 pattern
  rw [s2267, s2240]
  rfl
theorem s2269 (pattern : Twelve) : d14 (change pattern 2 12) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 2 12) else d5 (change pattern 2 12)) = d14 pattern
  rw [s2188, s2184]
  rfl
theorem s2270 (pattern : Twelve) : d21 (change pattern 2 12) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 2 12) else d13 (change pattern 2 12)) = d21 pattern
  rw [s2269, s2263]
  rfl
theorem s2271 (pattern : Twelve) : d821 (change pattern 2 12) = d821 pattern := by
  change (if pattern.i then d21 (change pattern 2 12) else d25 (change pattern 2 12)) = d821 pattern
  rw [s2270, s2186]
  rfl
theorem s2272 (pattern : Twelve) : d1289 (change pattern 2 12) = d1289 pattern := by
  change (if pattern.h then d42 (change pattern 2 12) else d821 (change pattern 2 12)) = d1289 pattern
  rw [s2189, s2271]
  rfl
theorem s2273 (pattern : Twelve) : d1300 (change pattern 2 12) = d1300 pattern := by
  change (if pattern.f then d6 (change pattern 2 12) else d1289 (change pattern 2 12)) = d1300 pattern
  rw [s2188, s2272]
  rfl
theorem s2274 (pattern : Twelve) : d1657 (change pattern 2 12) = d1657 pattern := by
  change (if pattern.e then d1300 (change pattern 2 12) else d1651 (change pattern 2 12)) = d1657 pattern
  rw [s2273, s2268]
  rfl
theorem s2275 (pattern : Twelve) : d1660 (change pattern 2 12) = d1660 pattern := by
  change (if pattern.j then d1657 (change pattern 2 12) else d1656 (change pattern 2 12)) = d1660 pattern
  rw [s2274, s2262]
  rfl
theorem s2276 (pattern : Twelve) : d1714 (change pattern 2 12) = d1660 pattern := by
  change d1660 (change pattern 2 12) = d1660 pattern
  exact s2275 pattern
theorem s2277 (pattern : Twelve) : d26 (change pattern 2 12) = d26 pattern := by
  change (if pattern.i then d1 (change pattern 2 12) else d0 (change pattern 2 12)) = d26 pattern
  rw [s2169, s2168]
  rfl
theorem s2278 (pattern : Twelve) : d50 (change pattern 2 12) = d50 pattern := by
  change (if pattern.h then d27 (change pattern 2 12) else d26 (change pattern 2 12)) = d50 pattern
  rw [s2172, s2277]
  rfl
theorem s2279 (pattern : Twelve) : d72 (change pattern 2 12) = d72 pattern := by
  change (if pattern.f then d50 (change pattern 2 12) else d0 (change pattern 2 12)) = d72 pattern
  rw [s2278, s2168]
  rfl
theorem s2280 (pattern : Twelve) : d18 (change pattern 2 12) = d18 pattern := by
  change (if pattern.k then d9 (change pattern 2 12) else d8 (change pattern 2 12)) = d18 pattern
  rw [s2196, s2225]
  rfl
theorem s2281 (pattern : Twelve) : d28 (change pattern 2 12) = d28 pattern := by
  change (if pattern.i then d18 (change pattern 2 12) else d17 (change pattern 2 12)) = d28 pattern
  rw [s2280, s2171]
  rfl
theorem s2282 (pattern : Twelve) : d51 (change pattern 2 12) = d51 pattern := by
  change (if pattern.h then d29 (change pattern 2 12) else d28 (change pattern 2 12)) = d51 pattern
  rw [s2239, s2281]
  rfl
theorem s2283 (pattern : Twelve) : d73 (change pattern 2 12) = d73 pattern := by
  change (if pattern.f then d51 (change pattern 2 12) else d0 (change pattern 2 12)) = d73 pattern
  rw [s2282, s2168]
  rfl
theorem s2284 (pattern : Twelve) : d91 (change pattern 2 12) = d91 pattern := by
  change (if pattern.e then d73 (change pattern 2 12) else d72 (change pattern 2 12)) = d91 pattern
  rw [s2283, s2279]
  rfl
theorem s2285 (pattern : Twelve) : d31 (change pattern 2 12) = d31 pattern := by
  change (if pattern.i then d20 (change pattern 2 12) else d0 (change pattern 2 12)) = d31 pattern
  rw [s2264, s2168]
  rfl
theorem s2286 (pattern : Twelve) : d52 (change pattern 2 12) = d52 pattern := by
  change (if pattern.h then d31 (change pattern 2 12) else d30 (change pattern 2 12)) = d52 pattern
  rw [s2285, s2193]
  rfl
theorem s2287 (pattern : Twelve) : d32 (change pattern 2 12) = d32 pattern := by
  change (if pattern.i then d21 (change pattern 2 12) else d17 (change pattern 2 12)) = d32 pattern
  rw [s2270, s2171]
  rfl
theorem s2288 (pattern : Twelve) : d53 (change pattern 2 12) = d53 pattern := by
  change (if pattern.h then d32 (change pattern 2 12) else d30 (change pattern 2 12)) = d53 pattern
  rw [s2287, s2193]
  rfl
theorem s2289 (pattern : Twelve) : d74 (change pattern 2 12) = d74 pattern := by
  change (if pattern.f then d53 (change pattern 2 12) else d52 (change pattern 2 12)) = d74 pattern
  rw [s2288, s2286]
  rfl
theorem s2290 (pattern : Twelve) : d22 (change pattern 2 12) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 2 12) else d14 (change pattern 2 12)) = d22 pattern
  rw [s2188, s2269]
  rfl
theorem s2291 (pattern : Twelve) : d33 (change pattern 2 12) = d33 pattern := by
  change (if pattern.i then d22 (change pattern 2 12) else d0 (change pattern 2 12)) = d33 pattern
  rw [s2290, s2168]
  rfl
theorem s2292 (pattern : Twelve) : d54 (change pattern 2 12) = d54 pattern := by
  change (if pattern.h then d33 (change pattern 2 12) else d30 (change pattern 2 12)) = d54 pattern
  rw [s2291, s2193]
  rfl
theorem s2293 (pattern : Twelve) : d55 (change pattern 2 12) = d55 pattern := by
  change (if pattern.h then d29 (change pattern 2 12) else d34 (change pattern 2 12)) = d55 pattern
  rw [s2239, s2198]
  rfl
theorem s2294 (pattern : Twelve) : d75 (change pattern 2 12) = d75 pattern := by
  change (if pattern.f then d55 (change pattern 2 12) else d54 (change pattern 2 12)) = d75 pattern
  rw [s2293, s2292]
  rfl
theorem s2295 (pattern : Twelve) : d92 (change pattern 2 12) = d92 pattern := by
  change (if pattern.e then d75 (change pattern 2 12) else d74 (change pattern 2 12)) = d92 pattern
  rw [s2294, s2289]
  rfl
theorem s2296 (pattern : Twelve) : d102 (change pattern 2 12) = d102 pattern := by
  change (if pattern.j then d92 (change pattern 2 12) else d91 (change pattern 2 12)) = d102 pattern
  rw [s2295, s2284]
  rfl
theorem s2297 (pattern : Twelve) : d76 (change pattern 2 12) = d76 pattern := by
  change (if pattern.f then d55 (change pattern 2 12) else d0 (change pattern 2 12)) = d76 pattern
  rw [s2293, s2168]
  rfl
theorem s2298 (pattern : Twelve) : d93 (change pattern 2 12) = d93 pattern := by
  change (if pattern.e then d76 (change pattern 2 12) else d72 (change pattern 2 12)) = d93 pattern
  rw [s2297, s2279]
  rfl
theorem s2299 (pattern : Twelve) : d57 (change pattern 2 12) = d57 pattern := by
  change (if pattern.h then d36 (change pattern 2 12) else d30 (change pattern 2 12)) = d57 pattern
  rw [s2202, s2193]
  rfl
theorem s2300 (pattern : Twelve) : d77 (change pattern 2 12) = d77 pattern := by
  change (if pattern.f then d57 (change pattern 2 12) else d56 (change pattern 2 12)) = d77 pattern
  rw [s2299, s2195]
  rfl
theorem s2301 (pattern : Twelve) : d78 (change pattern 2 12) = d78 pattern := by
  change (if pattern.f then d55 (change pattern 2 12) else d56 (change pattern 2 12)) = d78 pattern
  rw [s2293, s2195]
  rfl
theorem s2302 (pattern : Twelve) : d94 (change pattern 2 12) = d94 pattern := by
  change (if pattern.e then d78 (change pattern 2 12) else d77 (change pattern 2 12)) = d94 pattern
  rw [s2301, s2300]
  rfl
theorem s2303 (pattern : Twelve) : d103 (change pattern 2 12) = d103 pattern := by
  change (if pattern.j then d94 (change pattern 2 12) else d93 (change pattern 2 12)) = d103 pattern
  rw [s2302, s2298]
  rfl
theorem s2304 (pattern : Twelve) : d110 (change pattern 2 12) = d110 pattern := by
  change (if pattern.d then d103 (change pattern 2 12) else d102 (change pattern 2 12)) = d110 pattern
  rw [s2303, s2296]
  rfl
theorem s2305 (pattern : Twelve) : d345 (change pattern 2 12) = d110 pattern := by
  change d110 (change pattern 2 12) = d110 pattern
  exact s2304 pattern
theorem s2306 (pattern : Twelve) : d80 (change pattern 2 12) = d80 pattern := by
  change (if pattern.f then d55 (change pattern 2 12) else d30 (change pattern 2 12)) = d80 pattern
  rw [s2293, s2193]
  rfl
theorem s2307 (pattern : Twelve) : d97 (change pattern 2 12) = d97 pattern := by
  change (if pattern.e then d80 (change pattern 2 12) else d72 (change pattern 2 12)) = d97 pattern
  rw [s2306, s2279]
  rfl
theorem s2308 (pattern : Twelve) : d43 (change pattern 2 12) = d43 pattern := by
  change (if pattern.i then d21 (change pattern 2 12) else d1 (change pattern 2 12)) = d43 pattern
  rw [s2270, s2169]
  rfl
theorem s2309 (pattern : Twelve) : d62 (change pattern 2 12) = d62 pattern := by
  change (if pattern.h then d43 (change pattern 2 12) else d30 (change pattern 2 12)) = d62 pattern
  rw [s2308, s2193]
  rfl
theorem s2310 (pattern : Twelve) : d83 (change pattern 2 12) = d83 pattern := by
  change (if pattern.f then d62 (change pattern 2 12) else d52 (change pattern 2 12)) = d83 pattern
  rw [s2309, s2286]
  rfl
theorem s2311 (pattern : Twelve) : d44 (change pattern 2 12) = d44 pattern := by
  change (if pattern.i then d22 (change pattern 2 12) else d2 (change pattern 2 12)) = d44 pattern
  rw [s2290, s2177]
  rfl
theorem s2312 (pattern : Twelve) : d63 (change pattern 2 12) = d63 pattern := by
  change (if pattern.h then d44 (change pattern 2 12) else d30 (change pattern 2 12)) = d63 pattern
  rw [s2311, s2193]
  rfl
theorem s2313 (pattern : Twelve) : d64 (change pattern 2 12) = d64 pattern := by
  change (if pattern.h then d40 (change pattern 2 12) else d34 (change pattern 2 12)) = d64 pattern
  rw [s2248, s2198]
  rfl
theorem s2314 (pattern : Twelve) : d84 (change pattern 2 12) = d84 pattern := by
  change (if pattern.f then d64 (change pattern 2 12) else d63 (change pattern 2 12)) = d84 pattern
  rw [s2313, s2312]
  rfl
theorem s2315 (pattern : Twelve) : d98 (change pattern 2 12) = d98 pattern := by
  change (if pattern.e then d84 (change pattern 2 12) else d83 (change pattern 2 12)) = d98 pattern
  rw [s2314, s2310]
  rfl
theorem s2316 (pattern : Twelve) : d106 (change pattern 2 12) = d106 pattern := by
  change (if pattern.j then d98 (change pattern 2 12) else d97 (change pattern 2 12)) = d106 pattern
  rw [s2315, s2307]
  rfl
theorem s2317 (pattern : Twelve) : d65 (change pattern 2 12) = d65 pattern := by
  change (if pattern.h then d45 (change pattern 2 12) else d30 (change pattern 2 12)) = d65 pattern
  rw [s2211, s2193]
  rfl
theorem s2318 (pattern : Twelve) : d85 (change pattern 2 12) = d85 pattern := by
  change (if pattern.f then d65 (change pattern 2 12) else d56 (change pattern 2 12)) = d85 pattern
  rw [s2317, s2195]
  rfl
theorem s2319 (pattern : Twelve) : d66 (change pattern 2 12) = d66 pattern := by
  change (if pattern.h then d39 (change pattern 2 12) else d30 (change pattern 2 12)) = d66 pattern
  rw [s2214, s2193]
  rfl
theorem s2320 (pattern : Twelve) : d86 (change pattern 2 12) = d86 pattern := by
  change (if pattern.f then d64 (change pattern 2 12) else d66 (change pattern 2 12)) = d86 pattern
  rw [s2313, s2319]
  rfl
theorem s2321 (pattern : Twelve) : d99 (change pattern 2 12) = d99 pattern := by
  change (if pattern.e then d86 (change pattern 2 12) else d85 (change pattern 2 12)) = d99 pattern
  rw [s2320, s2318]
  rfl
theorem s2322 (pattern : Twelve) : d107 (change pattern 2 12) = d107 pattern := by
  change (if pattern.j then d99 (change pattern 2 12) else d97 (change pattern 2 12)) = d107 pattern
  rw [s2321, s2307]
  rfl
theorem s2323 (pattern : Twelve) : d112 (change pattern 2 12) = d112 pattern := by
  change (if pattern.d then d107 (change pattern 2 12) else d106 (change pattern 2 12)) = d112 pattern
  rw [s2322, s2316]
  rfl
theorem s2324 (pattern : Twelve) : d346 (change pattern 2 12) = d112 pattern := by
  change d112 (change pattern 2 12) = d112 pattern
  exact s2323 pattern
theorem s2325 (pattern : Twelve) : d348 (change pattern 2 12) = d2276 pattern := by
  change (if pattern.g then d346 (change pattern 2 12) else d345 (change pattern 2 12)) = d2276 pattern
  rw [s2324, s2305]
  rfl
theorem s2326 (pattern : Twelve) : d347 (change pattern 2 12) = d110 pattern := by
  change d110 (change pattern 2 12) = d110 pattern
  exact s2304 pattern
theorem s2327 (pattern : Twelve) : d349 (change pattern 2 12) = d2276 pattern := by
  change (if pattern.g then d346 (change pattern 2 12) else d347 (change pattern 2 12)) = d2276 pattern
  rw [s2324, s2326]
  rfl
theorem s2328 (pattern : Twelve) : d350 (change pattern 2 12) = d2276 pattern := by
  change (if pattern.b then d349 (change pattern 2 12) else d348 (change pattern 2 12)) = d2276 pattern
  rw [s2327, s2325]
  simp only [ite_self]
theorem s2329 (pattern : Twelve) : d351 (change pattern 2 12) = d2276 pattern := by
  change (if pattern.a then d349 (change pattern 2 12) else d350 (change pattern 2 12)) = d2276 pattern
  rw [s2327, s2328]
  simp only [ite_self]
theorem s2330 (pattern : Twelve) : d0 (change pattern 9 8) = d0 pattern := by
  rfl
theorem s2331 (pattern : Twelve) : d1 (change pattern 9 8) = d1 pattern := by
  rfl
theorem s2332 (pattern : Twelve) : d26 (change pattern 9 8) = d1 pattern := by
  change d1 (change pattern 9 8) = d1 pattern
  exact s2331 pattern
theorem s2333 (pattern : Twelve) : d27 (change pattern 9 8) = d1 pattern := by
  change d1 (change pattern 9 8) = d1 pattern
  exact s2331 pattern
theorem s2334 (pattern : Twelve) : d50 (change pattern 9 8) = d1 pattern := by
  change (if pattern.h then d27 (change pattern 9 8) else d26 (change pattern 9 8)) = d1 pattern
  rw [s2333, s2332]
  simp only [ite_self]
theorem s2335 (pattern : Twelve) : d72 (change pattern 9 8) = d1859 pattern := by
  change (if pattern.f then d50 (change pattern 9 8) else d0 (change pattern 9 8)) = d1859 pattern
  rw [s2334, s2330]
  rfl
theorem s2336 (pattern : Twelve) : d2 (change pattern 9 8) = d2 pattern := by
  rfl
theorem s2337 (pattern : Twelve) : d8 (change pattern 9 8) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 9 8) else d1 (change pattern 9 8)) = d8 pattern
  rw [s2336, s2331]
  rfl
theorem s2338 (pattern : Twelve) : d3 (change pattern 9 8) = d3 pattern := by
  rfl
theorem s2339 (pattern : Twelve) : d9 (change pattern 9 8) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 9 8) else d2 (change pattern 9 8)) = d9 pattern
  rw [s2338, s2336]
  rfl
theorem s2340 (pattern : Twelve) : d18 (change pattern 9 8) = d18 pattern := by
  change (if pattern.k then d9 (change pattern 9 8) else d8 (change pattern 9 8)) = d18 pattern
  rw [s2339, s2337]
  rfl
theorem s2341 (pattern : Twelve) : d28 (change pattern 9 8) = d18 pattern := by
  change d18 (change pattern 9 8) = d18 pattern
  exact s2340 pattern
theorem s2342 (pattern : Twelve) : d6 (change pattern 9 8) = d6 pattern := by
  rfl
theorem s2343 (pattern : Twelve) : d29 (change pattern 9 8) = d6 pattern := by
  change d6 (change pattern 9 8) = d6 pattern
  exact s2342 pattern
theorem s2344 (pattern : Twelve) : d51 (change pattern 9 8) = d2281 pattern := by
  change (if pattern.h then d29 (change pattern 9 8) else d28 (change pattern 9 8)) = d2281 pattern
  rw [s2343, s2341]
  rfl
theorem s2345 (pattern : Twelve) : d73 (change pattern 9 8) = d2282 pattern := by
  change (if pattern.f then d51 (change pattern 9 8) else d0 (change pattern 9 8)) = d2282 pattern
  rw [s2344, s2330]
  rfl
theorem s2346 (pattern : Twelve) : d91 (change pattern 9 8) = d2283 pattern := by
  change (if pattern.e then d73 (change pattern 9 8) else d72 (change pattern 9 8)) = d2283 pattern
  rw [s2345, s2335]
  rfl
theorem s2347 (pattern : Twelve) : d352 (change pattern 9 8) = d2283 pattern := by
  change d91 (change pattern 9 8) = d2283 pattern
  exact s2346 pattern
theorem s2348 (pattern : Twelve) : d23 (change pattern 9 8) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 9 8) else d2 (change pattern 9 8)) = d23 pattern
  rw [s2339, s2336]
  rfl
theorem s2349 (pattern : Twelve) : d34 (change pattern 9 8) = d23 pattern := by
  change d23 (change pattern 9 8) = d23 pattern
  exact s2348 pattern
theorem s2350 (pattern : Twelve) : d55 (change pattern 9 8) = d2284 pattern := by
  change (if pattern.h then d29 (change pattern 9 8) else d34 (change pattern 9 8)) = d2284 pattern
  rw [s2343, s2349]
  rfl
theorem s2351 (pattern : Twelve) : d76 (change pattern 9 8) = d2285 pattern := by
  change (if pattern.f then d55 (change pattern 9 8) else d0 (change pattern 9 8)) = d2285 pattern
  rw [s2350, s2330]
  rfl
theorem s2352 (pattern : Twelve) : d93 (change pattern 9 8) = d2286 pattern := by
  change (if pattern.e then d76 (change pattern 9 8) else d72 (change pattern 9 8)) = d2286 pattern
  rw [s2351, s2335]
  rfl
theorem s2353 (pattern : Twelve) : d353 (change pattern 9 8) = d2286 pattern := by
  change d93 (change pattern 9 8) = d2286 pattern
  exact s2352 pattern
theorem s2354 (pattern : Twelve) : d358 (change pattern 9 8) = d2287 pattern := by
  change (if pattern.d then d353 (change pattern 9 8) else d352 (change pattern 9 8)) = d2287 pattern
  rw [s2353, s2347]
  rfl
theorem s2355 (pattern : Twelve) : d354 (change pattern 9 8) = d2283 pattern := by
  change d91 (change pattern 9 8) = d2283 pattern
  exact s2346 pattern
theorem s2356 (pattern : Twelve) : d355 (change pattern 9 8) = d2286 pattern := by
  change d93 (change pattern 9 8) = d2286 pattern
  exact s2352 pattern
theorem s2357 (pattern : Twelve) : d359 (change pattern 9 8) = d2287 pattern := by
  change (if pattern.d then d355 (change pattern 9 8) else d354 (change pattern 9 8)) = d2287 pattern
  rw [s2356, s2355]
  rfl
theorem s2358 (pattern : Twelve) : d361 (change pattern 9 8) = d2287 pattern := by
  change (if pattern.c then d359 (change pattern 9 8) else d358 (change pattern 9 8)) = d2287 pattern
  rw [s2357, s2354]
  simp only [ite_self]
theorem s2359 (pattern : Twelve) : d30 (change pattern 9 8) = d2 pattern := by
  change d2 (change pattern 9 8) = d2 pattern
  exact s2336 pattern
theorem s2360 (pattern : Twelve) : d80 (change pattern 9 8) = d2288 pattern := by
  change (if pattern.f then d55 (change pattern 9 8) else d30 (change pattern 9 8)) = d2288 pattern
  rw [s2350, s2359]
  rfl
theorem s2361 (pattern : Twelve) : d97 (change pattern 9 8) = d2289 pattern := by
  change (if pattern.e then d80 (change pattern 9 8) else d72 (change pattern 9 8)) = d2289 pattern
  rw [s2360, s2335]
  rfl
theorem s2362 (pattern : Twelve) : d356 (change pattern 9 8) = d2289 pattern := by
  change d97 (change pattern 9 8) = d2289 pattern
  exact s2361 pattern
theorem s2363 (pattern : Twelve) : d362 (change pattern 9 8) = d2290 pattern := by
  change (if pattern.g then d356 (change pattern 9 8) else d361 (change pattern 9 8)) = d2290 pattern
  rw [s2362, s2358]
  rfl
theorem s2364 (pattern : Twelve) : d357 (change pattern 9 8) = d2283 pattern := by
  change d91 (change pattern 9 8) = d2283 pattern
  exact s2346 pattern
theorem s2365 (pattern : Twelve) : d360 (change pattern 9 8) = d2287 pattern := by
  change (if pattern.d then d355 (change pattern 9 8) else d357 (change pattern 9 8)) = d2287 pattern
  rw [s2356, s2364]
  rfl
theorem s2366 (pattern : Twelve) : d363 (change pattern 9 8) = d2290 pattern := by
  change (if pattern.g then d356 (change pattern 9 8) else d360 (change pattern 9 8)) = d2290 pattern
  rw [s2362, s2365]
  rfl
theorem s2367 (pattern : Twelve) : d364 (change pattern 9 8) = d2290 pattern := by
  change (if pattern.b then d363 (change pattern 9 8) else d362 (change pattern 9 8)) = d2290 pattern
  rw [s2366, s2363]
  simp only [ite_self]
theorem s2368 (pattern : Twelve) : d365 (change pattern 9 8) = d2290 pattern := by
  change (if pattern.a then d363 (change pattern 9 8) else d364 (change pattern 9 8)) = d2290 pattern
  rw [s2366, s2367]
  simp only [ite_self]
theorem s2369 (pattern : Twelve) : d816 (change pattern 9 8) = d1 pattern := by
  change d1 (change pattern 9 8) = d1 pattern
  exact s2331 pattern
theorem s2370 (pattern : Twelve) : d824 (change pattern 9 8) = d1 pattern := by
  change (if pattern.h then d816 (change pattern 9 8) else d27 (change pattern 9 8)) = d1 pattern
  rw [s2369, s2333]
  simp only [ite_self]
theorem s2371 (pattern : Twelve) : d838 (change pattern 9 8) = d1859 pattern := by
  change (if pattern.f then d824 (change pattern 9 8) else d0 (change pattern 9 8)) = d1859 pattern
  rw [s2370, s2330]
  rfl
theorem s2372 (pattern : Twelve) : d7 (change pattern 9 8) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 9 8) else d0 (change pattern 9 8)) = d7 pattern
  rw [s2331, s2330]
  rfl
theorem s2373 (pattern : Twelve) : d17 (change pattern 9 8) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 9 8) else d0 (change pattern 9 8)) = d17 pattern
  rw [s2372, s2330]
  rfl
theorem s2374 (pattern : Twelve) : d4 (change pattern 9 8) = d4 pattern := by
  rfl
theorem s2375 (pattern : Twelve) : d16 (change pattern 9 8) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 9 8) else d2 (change pattern 9 8)) = d16 pattern
  rw [s2374, s2336]
  rfl
theorem s2376 (pattern : Twelve) : d5 (change pattern 9 8) = d5 pattern := by
  rfl
theorem s2377 (pattern : Twelve) : d12 (change pattern 9 8) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 9 8) else d3 (change pattern 9 8)) = d12 pattern
  rw [s2376, s2338]
  rfl
theorem s2378 (pattern : Twelve) : d25 (change pattern 9 8) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 9 8) else d16 (change pattern 9 8)) = d25 pattern
  rw [s2377, s2375]
  rfl
theorem s2379 (pattern : Twelve) : d817 (change pattern 9 8) = d25 pattern := by
  change d25 (change pattern 9 8) = d25 pattern
  exact s2378 pattern
theorem s2380 (pattern : Twelve) : d42 (change pattern 9 8) = d6 pattern := by
  change d6 (change pattern 9 8) = d6 pattern
  exact s2342 pattern
theorem s2381 (pattern : Twelve) : d825 (change pattern 9 8) = d1690 pattern := by
  change (if pattern.h then d42 (change pattern 9 8) else d817 (change pattern 9 8)) = d1690 pattern
  rw [s2380, s2379]
  rfl
theorem s2382 (pattern : Twelve) : d839 (change pattern 9 8) = d2291 pattern := by
  change (if pattern.f then d825 (change pattern 9 8) else d17 (change pattern 9 8)) = d2291 pattern
  rw [s2381, s2373]
  rfl
theorem s2383 (pattern : Twelve) : d853 (change pattern 9 8) = d2292 pattern := by
  change (if pattern.e then d839 (change pattern 9 8) else d838 (change pattern 9 8)) = d2292 pattern
  rw [s2382, s2371]
  rfl
theorem s2384 (pattern : Twelve) : d1018 (change pattern 9 8) = d2292 pattern := by
  change d853 (change pattern 9 8) = d2292 pattern
  exact s2383 pattern
theorem s2385 (pattern : Twelve) : d1019 (change pattern 9 8) = d2292 pattern := by
  change d853 (change pattern 9 8) = d2292 pattern
  exact s2383 pattern
theorem s2386 (pattern : Twelve) : d1023 (change pattern 9 8) = d2292 pattern := by
  change (if pattern.d then d1019 (change pattern 9 8) else d1018 (change pattern 9 8)) = d2292 pattern
  rw [s2385, s2384]
  simp only [ite_self]
theorem s2387 (pattern : Twelve) : d1020 (change pattern 9 8) = d2292 pattern := by
  change d853 (change pattern 9 8) = d2292 pattern
  exact s2383 pattern
theorem s2388 (pattern : Twelve) : d1021 (change pattern 9 8) = d2292 pattern := by
  change d853 (change pattern 9 8) = d2292 pattern
  exact s2383 pattern
theorem s2389 (pattern : Twelve) : d1024 (change pattern 9 8) = d2292 pattern := by
  change (if pattern.d then d1021 (change pattern 9 8) else d1020 (change pattern 9 8)) = d2292 pattern
  rw [s2388, s2387]
  simp only [ite_self]
theorem s2390 (pattern : Twelve) : d1025 (change pattern 9 8) = d2292 pattern := by
  change (if pattern.c then d1024 (change pattern 9 8) else d1023 (change pattern 9 8)) = d2292 pattern
  rw [s2389, s2386]
  simp only [ite_self]
theorem s2391 (pattern : Twelve) : d823 (change pattern 9 8) = d2 pattern := by
  change d2 (change pattern 9 8) = d2 pattern
  exact s2336 pattern
theorem s2392 (pattern : Twelve) : d846 (change pattern 9 8) = d2293 pattern := by
  change (if pattern.f then d825 (change pattern 9 8) else d823 (change pattern 9 8)) = d2293 pattern
  rw [s2381, s2391]
  rfl
theorem s2393 (pattern : Twelve) : d857 (change pattern 9 8) = d2294 pattern := by
  change (if pattern.e then d846 (change pattern 9 8) else d838 (change pattern 9 8)) = d2294 pattern
  rw [s2392, s2371]
  rfl
theorem s2394 (pattern : Twelve) : d1022 (change pattern 9 8) = d2294 pattern := by
  change d857 (change pattern 9 8) = d2294 pattern
  exact s2393 pattern
theorem s2395 (pattern : Twelve) : d1026 (change pattern 9 8) = d2295 pattern := by
  change (if pattern.g then d1022 (change pattern 9 8) else d1025 (change pattern 9 8)) = d2295 pattern
  rw [s2394, s2390]
  rfl
theorem s2396 (pattern : Twelve) : d1027 (change pattern 9 8) = d2295 pattern := by
  change (if pattern.g then d1022 (change pattern 9 8) else d1021 (change pattern 9 8)) = d2295 pattern
  rw [s2394, s2388]
  rfl
theorem s2397 (pattern : Twelve) : d1028 (change pattern 9 8) = d2295 pattern := by
  change (if pattern.b then d1027 (change pattern 9 8) else d1026 (change pattern 9 8)) = d2295 pattern
  rw [s2396, s2395]
  simp only [ite_self]
theorem s2398 (pattern : Twelve) : d1029 (change pattern 9 8) = d2295 pattern := by
  change (if pattern.a then d1027 (change pattern 9 8) else d1028 (change pattern 9 8)) = d2295 pattern
  rw [s2396, s2397]
  simp only [ite_self]
theorem s2399 (pattern : Twelve) : d872 (change pattern 9 8) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 9 8) else d1 (change pattern 9 8)) = d872 pattern
  rw [s2337, s2331]
  rfl
end NetHack.Sokoban21.Diagram
