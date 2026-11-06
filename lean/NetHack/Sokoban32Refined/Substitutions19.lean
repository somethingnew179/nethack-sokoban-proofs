/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions18
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2280 (p : Pattern) : d6 (change p 138 (some 139)) = d6 p := by
  change (if p 159 then d5 (change p 138 (some 139)) else d4 (change p 138 (some 139))) = d6 p
  rw [sub2279, sub2278]
  rfl
theorem sub2281 (p : Pattern) : d7 (change p 138 (some 139)) = d7 p := by
  change (if p 159 then d2 (change p 138 (some 139)) else d4 (change p 138 (some 139))) = d7 p
  rw [sub2276, sub2278]
  rfl
theorem sub2282 (p : Pattern) : d8 (change p 138 (some 139)) = d8 p := by
  change (if p 158 then d7 (change p 138 (some 139)) else d6 (change p 138 (some 139))) = d8 p
  rw [sub2281, sub2280]
  rfl
theorem sub2283 (p : Pattern) : d389 (change p 138 (some 139)) = d8 p := by
  change d8 (change p 138 (some 139)) = d8 p
  exact sub2282 p
theorem sub2284 (p : Pattern) : d17 (change p 138 (some 139)) = d17 p := by
  change (if p 160 then d2 (change p 138 (some 139)) else d3 (change p 138 (some 139))) = d17 p
  rw [sub2276, sub2277]
  rfl
theorem sub2285 (p : Pattern) : d18 (change p 138 (some 139)) = d18 p := by
  change (if p 159 then d17 (change p 138 (some 139)) else d4 (change p 138 (some 139))) = d18 p
  rw [sub2284, sub2278]
  rfl
theorem sub2286 (p : Pattern) : d19 (change p 138 (some 139)) = d19 p := by
  change (if p 159 then d2 (change p 138 (some 139)) else d17 (change p 138 (some 139))) = d19 p
  rw [sub2276, sub2284]
  rfl
theorem sub2287 (p : Pattern) : d20 (change p 138 (some 139)) = d20 p := by
  change (if p 158 then d19 (change p 138 (some 139)) else d18 (change p 138 (some 139))) = d20 p
  rw [sub2286, sub2285]
  rfl
theorem sub2288 (p : Pattern) : d390 (change p 138 (some 139)) = d20 p := by
  change d20 (change p 138 (some 139)) = d20 p
  exact sub2287 p
theorem sub2289 (p : Pattern) : d391 (change p 138 (some 139)) = d1097 p := by
  change (if p 134 then d390 (change p 138 (some 139)) else d389 (change p 138 (some 139))) = d1097 p
  rw [sub2288, sub2283]
  rfl
theorem sub2290 (p : Pattern) : d392 (change p 138 (some 139)) = d1098 p := by
  change (if p 133 then d391 (change p 138 (some 139)) else d389 (change p 138 (some 139))) = d1098 p
  rw [sub2289, sub2283]
  rfl
theorem sub2291 (p : Pattern) : d1 (change p 138 (some 139)) = d1 p := by
  rfl
theorem sub2292 (p : Pattern) : d29 (change p 138 (some 139)) = d29 p := by
  change (if p 161 then d1 (change p 138 (some 139)) else d0 (change p 138 (some 139))) = d29 p
  rw [sub2291, sub2275]
  rfl
theorem sub2293 (p : Pattern) : d30 (change p 138 (some 139)) = d30 p := by
  change (if p 160 then d2 (change p 138 (some 139)) else d29 (change p 138 (some 139))) = d30 p
  rw [sub2276, sub2292]
  rfl
theorem sub2294 (p : Pattern) : d31 (change p 138 (some 139)) = d31 p := by
  change (if p 159 then d30 (change p 138 (some 139)) else d4 (change p 138 (some 139))) = d31 p
  rw [sub2293, sub2278]
  rfl
theorem sub2295 (p : Pattern) : d32 (change p 138 (some 139)) = d32 p := by
  change (if p 159 then d2 (change p 138 (some 139)) else d30 (change p 138 (some 139))) = d32 p
  rw [sub2276, sub2293]
  rfl
theorem sub2296 (p : Pattern) : d33 (change p 138 (some 139)) = d33 p := by
  change (if p 158 then d32 (change p 138 (some 139)) else d31 (change p 138 (some 139))) = d33 p
  rw [sub2295, sub2294]
  rfl
theorem sub2297 (p : Pattern) : d393 (change p 138 (some 139)) = d33 p := by
  change d33 (change p 138 (some 139)) = d33 p
  exact sub2296 p
theorem sub2298 (p : Pattern) : d394 (change p 138 (some 139)) = d1099 p := by
  change (if p 134 then d393 (change p 138 (some 139)) else d389 (change p 138 (some 139))) = d1099 p
  rw [sub2297, sub2283]
  rfl
theorem sub2299 (p : Pattern) : d37 (change p 138 (some 139)) = d37 p := by
  change (if p 159 then d2 (change p 138 (some 139)) else d5 (change p 138 (some 139))) = d37 p
  rw [sub2276, sub2279]
  rfl
theorem sub2300 (p : Pattern) : d38 (change p 138 (some 139)) = d38 p := by
  change (if p 158 then d37 (change p 138 (some 139)) else d6 (change p 138 (some 139))) = d38 p
  rw [sub2299, sub2280]
  rfl
theorem sub2301 (p : Pattern) : d395 (change p 138 (some 139)) = d38 p := by
  change d38 (change p 138 (some 139)) = d38 p
  exact sub2300 p
theorem sub2302 (p : Pattern) : d396 (change p 138 (some 139)) = d1100 p := by
  change (if p 134 then d390 (change p 138 (some 139)) else d395 (change p 138 (some 139))) = d1100 p
  rw [sub2288, sub2301]
  rfl
theorem sub2303 (p : Pattern) : d397 (change p 138 (some 139)) = d1101 p := by
  change (if p 133 then d396 (change p 138 (some 139)) else d394 (change p 138 (some 139))) = d1101 p
  rw [sub2302, sub2298]
  rfl
theorem sub2304 (p : Pattern) : d398 (change p 138 (some 139)) = d1102 p := by
  change (if p 132 then d397 (change p 138 (some 139)) else d392 (change p 138 (some 139))) = d1102 p
  rw [sub2303, sub2290]
  rfl
theorem sub2305 (p : Pattern) : d9 (change p 138 (some 139)) = d9 p := by
  change (if p 161 then d2 (change p 138 (some 139)) else d1 (change p 138 (some 139))) = d9 p
  rw [sub2276, sub2291]
  rfl
theorem sub2306 (p : Pattern) : d10 (change p 138 (some 139)) = d10 p := by
  change (if p 160 then d9 (change p 138 (some 139)) else d1 (change p 138 (some 139))) = d10 p
  rw [sub2305, sub2291]
  rfl
theorem sub2307 (p : Pattern) : d11 (change p 138 (some 139)) = d11 p := by
  change (if p 160 then d2 (change p 138 (some 139)) else d1 (change p 138 (some 139))) = d11 p
  rw [sub2276, sub2291]
  rfl
theorem sub2308 (p : Pattern) : d12 (change p 138 (some 139)) = d12 p := by
  change (if p 159 then d11 (change p 138 (some 139)) else d10 (change p 138 (some 139))) = d12 p
  rw [sub2307, sub2306]
  rfl
theorem sub2309 (p : Pattern) : d13 (change p 138 (some 139)) = d13 p := by
  change (if p 159 then d2 (change p 138 (some 139)) else d10 (change p 138 (some 139))) = d13 p
  rw [sub2276, sub2306]
  rfl
theorem sub2310 (p : Pattern) : d14 (change p 138 (some 139)) = d14 p := by
  change (if p 158 then d13 (change p 138 (some 139)) else d12 (change p 138 (some 139))) = d14 p
  rw [sub2309, sub2308]
  rfl
theorem sub2311 (p : Pattern) : d15 (change p 138 (some 139)) = d14 p := by
  change d14 (change p 138 (some 139)) = d14 p
  exact sub2310 p
theorem sub2312 (p : Pattern) : d399 (change p 138 (some 139)) = d14 p := by
  change d15 (change p 138 (some 139)) = d14 p
  exact sub2311 p
theorem sub2313 (p : Pattern) : d21 (change p 138 (some 139)) = d21 p := by
  change (if p 160 then d2 (change p 138 (some 139)) else d9 (change p 138 (some 139))) = d21 p
  rw [sub2276, sub2305]
  rfl
theorem sub2314 (p : Pattern) : d22 (change p 138 (some 139)) = d22 p := by
  change (if p 159 then d21 (change p 138 (some 139)) else d10 (change p 138 (some 139))) = d22 p
  rw [sub2313, sub2306]
  rfl
theorem sub2315 (p : Pattern) : d23 (change p 138 (some 139)) = d23 p := by
  change (if p 159 then d2 (change p 138 (some 139)) else d21 (change p 138 (some 139))) = d23 p
  rw [sub2276, sub2313]
  rfl
theorem sub2316 (p : Pattern) : d24 (change p 138 (some 139)) = d24 p := by
  change (if p 158 then d23 (change p 138 (some 139)) else d22 (change p 138 (some 139))) = d24 p
  rw [sub2315, sub2314]
  rfl
theorem sub2317 (p : Pattern) : d25 (change p 138 (some 139)) = d24 p := by
  change d24 (change p 138 (some 139)) = d24 p
  exact sub2316 p
theorem sub2318 (p : Pattern) : d400 (change p 138 (some 139)) = d24 p := by
  change d25 (change p 138 (some 139)) = d24 p
  exact sub2317 p
theorem sub2319 (p : Pattern) : d401 (change p 138 (some 139)) = d1107 p := by
  change (if p 134 then d400 (change p 138 (some 139)) else d399 (change p 138 (some 139))) = d1107 p
  rw [sub2318, sub2312]
  rfl
theorem sub2320 (p : Pattern) : d402 (change p 138 (some 139)) = d1108 p := by
  change (if p 133 then d401 (change p 138 (some 139)) else d399 (change p 138 (some 139))) = d1108 p
  rw [sub2319, sub2312]
  rfl
theorem sub2321 (p : Pattern) : d34 (change p 138 (some 139)) = d24 p := by
  change d24 (change p 138 (some 139)) = d24 p
  exact sub2316 p
theorem sub2322 (p : Pattern) : d403 (change p 138 (some 139)) = d24 p := by
  change d34 (change p 138 (some 139)) = d24 p
  exact sub2321 p
theorem sub2323 (p : Pattern) : d404 (change p 138 (some 139)) = d1107 p := by
  change (if p 134 then d403 (change p 138 (some 139)) else d399 (change p 138 (some 139))) = d1107 p
  rw [sub2322, sub2312]
  rfl
theorem sub2324 (p : Pattern) : d39 (change p 138 (some 139)) = d39 p := by
  change (if p 159 then d2 (change p 138 (some 139)) else d11 (change p 138 (some 139))) = d39 p
  rw [sub2276, sub2307]
  rfl
theorem sub2325 (p : Pattern) : d40 (change p 138 (some 139)) = d40 p := by
  change (if p 158 then d39 (change p 138 (some 139)) else d12 (change p 138 (some 139))) = d40 p
  rw [sub2324, sub2308]
  rfl
theorem sub2326 (p : Pattern) : d41 (change p 138 (some 139)) = d40 p := by
  change d40 (change p 138 (some 139)) = d40 p
  exact sub2325 p
theorem sub2327 (p : Pattern) : d405 (change p 138 (some 139)) = d40 p := by
  change d41 (change p 138 (some 139)) = d40 p
  exact sub2326 p
theorem sub2328 (p : Pattern) : d406 (change p 138 (some 139)) = d1103 p := by
  change (if p 134 then d400 (change p 138 (some 139)) else d405 (change p 138 (some 139))) = d1103 p
  rw [sub2318, sub2327]
  rfl
theorem sub2329 (p : Pattern) : d407 (change p 138 (some 139)) = d1109 p := by
  change (if p 133 then d406 (change p 138 (some 139)) else d404 (change p 138 (some 139))) = d1109 p
  rw [sub2328, sub2323]
  rfl
theorem sub2330 (p : Pattern) : d408 (change p 138 (some 139)) = d1110 p := by
  change (if p 132 then d407 (change p 138 (some 139)) else d402 (change p 138 (some 139))) = d1110 p
  rw [sub2329, sub2320]
  rfl
theorem sub2331 (p : Pattern) : d409 (change p 138 (some 139)) = d1111 p := by
  change (if p 112 then d408 (change p 138 (some 139)) else d398 (change p 138 (some 139))) = d1111 p
  rw [sub2330, sub2304]
  rfl
theorem sub2332 (p : Pattern) : d410 (change p 138 (some 139)) = d40 p := by
  change d40 (change p 138 (some 139)) = d40 p
  exact sub2325 p
theorem sub2333 (p : Pattern) : d411 (change p 138 (some 139)) = d24 p := by
  change d24 (change p 138 (some 139)) = d24 p
  exact sub2316 p
theorem sub2334 (p : Pattern) : d412 (change p 138 (some 139)) = d1103 p := by
  change (if p 134 then d411 (change p 138 (some 139)) else d410 (change p 138 (some 139))) = d1103 p
  rw [sub2333, sub2332]
  rfl
theorem sub2335 (p : Pattern) : d413 (change p 138 (some 139)) = d1104 p := by
  change (if p 133 then d412 (change p 138 (some 139)) else d391 (change p 138 (some 139))) = d1104 p
  rw [sub2334, sub2289]
  rfl
theorem sub2336 (p : Pattern) : d414 (change p 138 (some 139)) = d1105 p := by
  change (if p 132 then d413 (change p 138 (some 139)) else d392 (change p 138 (some 139))) = d1105 p
  rw [sub2335, sub2290]
  rfl
theorem sub2337 (p : Pattern) : d68 (change p 138 (some 139)) = d2 p := by
  change d2 (change p 138 (some 139)) = d2 p
  exact sub2276 p
theorem sub2338 (p : Pattern) : d199 (change p 138 (some 139)) = d2 p := by
  change d68 (change p 138 (some 139)) = d2 p
  exact sub2337 p
theorem sub2339 (p : Pattern) : d70 (change p 138 (some 139)) = d2 p := by
  change d2 (change p 138 (some 139)) = d2 p
  exact sub2276 p
theorem sub2340 (p : Pattern) : d200 (change p 138 (some 139)) = d2 p := by
  change d70 (change p 138 (some 139)) = d2 p
  exact sub2339 p
theorem sub2341 (p : Pattern) : d201 (change p 138 (some 139)) = d2 p := by
  change (if p 134 then d200 (change p 138 (some 139)) else d199 (change p 138 (some 139))) = d2 p
  rw [sub2340, sub2338]
  simp only [ite_self]
theorem sub2342 (p : Pattern) : d415 (change p 138 (some 139)) = d1366 p := by
  change (if p 133 then d201 (change p 138 (some 139)) else d391 (change p 138 (some 139))) = d1366 p
  rw [sub2341, sub2289]
  rfl
theorem sub2343 (p : Pattern) : d416 (change p 138 (some 139)) = d1367 p := by
  change (if p 132 then d415 (change p 138 (some 139)) else d392 (change p 138 (some 139))) = d1367 p
  rw [sub2342, sub2290]
  rfl
theorem sub2344 (p : Pattern) : d417 (change p 138 (some 139)) = d1368 p := by
  change (if p 113 then d416 (change p 138 (some 139)) else d414 (change p 138 (some 139))) = d1368 p
  rw [sub2343, sub2336]
  rfl
theorem sub2345 (p : Pattern) : d418 (change p 138 (some 139)) = d1112 p := by
  change (if p 133 then d201 (change p 138 (some 139)) else d401 (change p 138 (some 139))) = d1112 p
  rw [sub2341, sub2319]
  rfl
theorem sub2346 (p : Pattern) : d419 (change p 138 (some 139)) = d1113 p := by
  change (if p 132 then d418 (change p 138 (some 139)) else d402 (change p 138 (some 139))) = d1113 p
  rw [sub2345, sub2320]
  rfl
theorem sub2347 (p : Pattern) : d420 (change p 138 (some 139)) = d1369 p := by
  change (if p 112 then d419 (change p 138 (some 139)) else d417 (change p 138 (some 139))) = d1369 p
  rw [sub2346, sub2344]
  rfl
theorem sub2348 (p : Pattern) : d421 (change p 138 (some 139)) = d1370 p := by
  change (if p 106 then d420 (change p 138 (some 139)) else d409 (change p 138 (some 139))) = d1370 p
  rw [sub2347, sub2331]
  rfl
theorem sub2349 (p : Pattern) : d422 (change p 138 (some 139)) = d14 p := by
  change d14 (change p 138 (some 139)) = d14 p
  exact sub2310 p
theorem sub2350 (p : Pattern) : d423 (change p 138 (some 139)) = d1107 p := by
  change (if p 134 then d411 (change p 138 (some 139)) else d422 (change p 138 (some 139))) = d1107 p
  rw [sub2333, sub2349]
  rfl
theorem sub2351 (p : Pattern) : d424 (change p 138 (some 139)) = d1108 p := by
  change (if p 133 then d423 (change p 138 (some 139)) else d422 (change p 138 (some 139))) = d1108 p
  rw [sub2350, sub2349]
  rfl
theorem sub2352 (p : Pattern) : d425 (change p 138 (some 139)) = d1109 p := by
  change (if p 133 then d412 (change p 138 (some 139)) else d423 (change p 138 (some 139))) = d1109 p
  rw [sub2334, sub2350]
  rfl
theorem sub2353 (p : Pattern) : d426 (change p 138 (some 139)) = d1110 p := by
  change (if p 132 then d425 (change p 138 (some 139)) else d424 (change p 138 (some 139))) = d1110 p
  rw [sub2352, sub2351]
  rfl
theorem sub2354 (p : Pattern) : d427 (change p 138 (some 139)) = d1111 p := by
  change (if p 112 then d426 (change p 138 (some 139)) else d398 (change p 138 (some 139))) = d1111 p
  rw [sub2353, sub2304]
  rfl
theorem sub2355 (p : Pattern) : d428 (change p 138 (some 139)) = d1112 p := by
  change (if p 133 then d2 (change p 138 (some 139)) else d423 (change p 138 (some 139))) = d1112 p
  rw [sub2276, sub2350]
  rfl
theorem sub2356 (p : Pattern) : d429 (change p 138 (some 139)) = d1113 p := by
  change (if p 132 then d428 (change p 138 (some 139)) else d424 (change p 138 (some 139))) = d1113 p
  rw [sub2355, sub2351]
  rfl
theorem sub2357 (p : Pattern) : d97 (change p 138 (some 139)) = d2 p := by
  change d2 (change p 138 (some 139)) = d2 p
  exact sub2276 p
theorem sub2358 (p : Pattern) : d430 (change p 138 (some 139)) = d2 p := by
  change d97 (change p 138 (some 139)) = d2 p
  exact sub2357 p
theorem sub2359 (p : Pattern) : d431 (change p 138 (some 139)) = d2 p := by
  change (if p 134 then d200 (change p 138 (some 139)) else d430 (change p 138 (some 139))) = d2 p
  rw [sub2340, sub2358]
  simp only [ite_self]
theorem sub2360 (p : Pattern) : d432 (change p 138 (some 139)) = d2 p := by
  change (if p 133 then d431 (change p 138 (some 139)) else d430 (change p 138 (some 139))) = d2 p
  rw [sub2359, sub2358]
  simp only [ite_self]
theorem sub2361 (p : Pattern) : d433 (change p 138 (some 139)) = d2 p := by
  change (if p 133 then d2 (change p 138 (some 139)) else d431 (change p 138 (some 139))) = d2 p
  rw [sub2276, sub2359]
  simp only [ite_self]
theorem sub2362 (p : Pattern) : d434 (change p 138 (some 139)) = d2 p := by
  change (if p 132 then d433 (change p 138 (some 139)) else d432 (change p 138 (some 139))) = d2 p
  rw [sub2361, sub2360]
  simp only [ite_self]
theorem sub2363 (p : Pattern) : d435 (change p 138 (some 139)) = d1117 p := by
  change (if p 113 then d434 (change p 138 (some 139)) else d429 (change p 138 (some 139))) = d1117 p
  rw [sub2362, sub2356]
  rfl
theorem sub2364 (p : Pattern) : d436 (change p 138 (some 139)) = d1371 p := by
  change (if p 112 then d435 (change p 138 (some 139)) else d416 (change p 138 (some 139))) = d1371 p
  rw [sub2363, sub2343]
  rfl
theorem sub2365 (p : Pattern) : d437 (change p 138 (some 139)) = d1372 p := by
  change (if p 106 then d436 (change p 138 (some 139)) else d427 (change p 138 (some 139))) = d1372 p
  rw [sub2364, sub2354]
  rfl
theorem sub2366 (p : Pattern) : d438 (change p 138 (some 139)) = d1373 p := by
  change (if p 86 then d437 (change p 138 (some 139)) else d421 (change p 138 (some 139))) = d1373 p
  rw [sub2365, sub2348]
  rfl
theorem sub2367 (p : Pattern) : d439 (change p 138 (some 139)) = d1374 p := by
  change (if p 112 then d419 (change p 138 (some 139)) else d416 (change p 138 (some 139))) = d1374 p
  rw [sub2346, sub2343]
  rfl
theorem sub2368 (p : Pattern) : d440 (change p 138 (some 139)) = d1375 p := by
  change (if p 106 then d439 (change p 138 (some 139)) else d409 (change p 138 (some 139))) = d1375 p
  rw [sub2367, sub2331]
  rfl
theorem sub2369 (p : Pattern) : d119 (change p 138 (some 139)) = d20 p := by
  change d20 (change p 138 (some 139)) = d20 p
  exact sub2287 p
theorem sub2370 (p : Pattern) : d441 (change p 138 (some 139)) = d20 p := by
  change d119 (change p 138 (some 139)) = d20 p
  exact sub2369 p
theorem sub2371 (p : Pattern) : d442 (change p 138 (some 139)) = d1097 p := by
  change (if p 134 then d441 (change p 138 (some 139)) else d389 (change p 138 (some 139))) = d1097 p
  rw [sub2370, sub2283]
  rfl
theorem sub2372 (p : Pattern) : d443 (change p 138 (some 139)) = d1376 p := by
  change (if p 133 then d396 (change p 138 (some 139)) else d442 (change p 138 (some 139))) = d1376 p
  rw [sub2302, sub2371]
  rfl
theorem sub2373 (p : Pattern) : d444 (change p 138 (some 139)) = d1377 p := by
  change (if p 132 then d443 (change p 138 (some 139)) else d392 (change p 138 (some 139))) = d1377 p
  rw [sub2372, sub2290]
  rfl
theorem sub2374 (p : Pattern) : d445 (change p 138 (some 139)) = d1378 p := by
  change (if p 113 then d444 (change p 138 (some 139)) else d398 (change p 138 (some 139))) = d1378 p
  rw [sub2373, sub2304]
  rfl
theorem sub2375 (p : Pattern) : d446 (change p 138 (some 139)) = d2 p := by
  change (if p 133 then d201 (change p 138 (some 139)) else d431 (change p 138 (some 139))) = d2 p
  rw [sub2341, sub2359]
  simp only [ite_self]
theorem sub2376 (p : Pattern) : d447 (change p 138 (some 139)) = d2 p := by
  change (if p 132 then d446 (change p 138 (some 139)) else d432 (change p 138 (some 139))) = d2 p
  rw [sub2375, sub2360]
  simp only [ite_self]
theorem sub2377 (p : Pattern) : d448 (change p 138 (some 139)) = d1379 p := by
  change (if p 113 then d447 (change p 138 (some 139)) else d426 (change p 138 (some 139))) = d1379 p
  rw [sub2376, sub2353]
  rfl
theorem sub2378 (p : Pattern) : d449 (change p 138 (some 139)) = d1380 p := by
  change (if p 112 then d448 (change p 138 (some 139)) else d445 (change p 138 (some 139))) = d1380 p
  rw [sub2377, sub2374]
  rfl
theorem sub2379 (p : Pattern) : d450 (change p 138 (some 139)) = d1381 p := by
  change (if p 113 then d419 (change p 138 (some 139)) else d416 (change p 138 (some 139))) = d1381 p
  rw [sub2346, sub2343]
  rfl
theorem sub2380 (p : Pattern) : d451 (change p 138 (some 139)) = d2 p := by
  change (if p 113 then d2 (change p 138 (some 139)) else d434 (change p 138 (some 139))) = d2 p
  rw [sub2276, sub2362]
  simp only [ite_self]
theorem sub2381 (p : Pattern) : d452 (change p 138 (some 139)) = d1382 p := by
  change (if p 112 then d451 (change p 138 (some 139)) else d450 (change p 138 (some 139))) = d1382 p
  rw [sub2380, sub2379]
  rfl
theorem sub2382 (p : Pattern) : d453 (change p 138 (some 139)) = d1383 p := by
  change (if p 106 then d452 (change p 138 (some 139)) else d449 (change p 138 (some 139))) = d1383 p
  rw [sub2381, sub2378]
  rfl
theorem sub2383 (p : Pattern) : d454 (change p 138 (some 139)) = d1384 p := by
  change (if p 86 then d453 (change p 138 (some 139)) else d440 (change p 138 (some 139))) = d1384 p
  rw [sub2382, sub2368]
  rfl
theorem sub2384 (p : Pattern) : d455 (change p 138 (some 139)) = d1385 p := by
  change (if p 80 then d454 (change p 138 (some 139)) else d438 (change p 138 (some 139))) = d1385 p
  rw [sub2383, sub2366]
  rfl
theorem sub2385 (p : Pattern) : d0 (change p 112 (some 86)) = d0 p := by
  rfl
theorem sub2386 (p : Pattern) : d2 (change p 112 (some 86)) = d2 p := by
  rfl
theorem sub2387 (p : Pattern) : d3 (change p 112 (some 86)) = d3 p := by
  change (if p 161 then d2 (change p 112 (some 86)) else d0 (change p 112 (some 86))) = d3 p
  rw [sub2386, sub2385]
  rfl
theorem sub2388 (p : Pattern) : d4 (change p 112 (some 86)) = d4 p := by
  change (if p 160 then d3 (change p 112 (some 86)) else d0 (change p 112 (some 86))) = d4 p
  rw [sub2387, sub2385]
  rfl
theorem sub2389 (p : Pattern) : d5 (change p 112 (some 86)) = d5 p := by
  change (if p 160 then d2 (change p 112 (some 86)) else d0 (change p 112 (some 86))) = d5 p
  rw [sub2386, sub2385]
  rfl
theorem sub2390 (p : Pattern) : d6 (change p 112 (some 86)) = d6 p := by
  change (if p 159 then d5 (change p 112 (some 86)) else d4 (change p 112 (some 86))) = d6 p
  rw [sub2389, sub2388]
  rfl
theorem sub2391 (p : Pattern) : d7 (change p 112 (some 86)) = d7 p := by
  change (if p 159 then d2 (change p 112 (some 86)) else d4 (change p 112 (some 86))) = d7 p
  rw [sub2386, sub2388]
  rfl
theorem sub2392 (p : Pattern) : d8 (change p 112 (some 86)) = d8 p := by
  change (if p 158 then d7 (change p 112 (some 86)) else d6 (change p 112 (some 86))) = d8 p
  rw [sub2391, sub2390]
  rfl
theorem sub2393 (p : Pattern) : d1 (change p 112 (some 86)) = d1 p := by
  rfl
theorem sub2394 (p : Pattern) : d9 (change p 112 (some 86)) = d9 p := by
  change (if p 161 then d2 (change p 112 (some 86)) else d1 (change p 112 (some 86))) = d9 p
  rw [sub2386, sub2393]
  rfl
theorem sub2395 (p : Pattern) : d10 (change p 112 (some 86)) = d10 p := by
  change (if p 160 then d9 (change p 112 (some 86)) else d1 (change p 112 (some 86))) = d10 p
  rw [sub2394, sub2393]
  rfl
theorem sub2396 (p : Pattern) : d11 (change p 112 (some 86)) = d11 p := by
  change (if p 160 then d2 (change p 112 (some 86)) else d1 (change p 112 (some 86))) = d11 p
  rw [sub2386, sub2393]
  rfl
theorem sub2397 (p : Pattern) : d12 (change p 112 (some 86)) = d12 p := by
  change (if p 159 then d11 (change p 112 (some 86)) else d10 (change p 112 (some 86))) = d12 p
  rw [sub2396, sub2395]
  rfl
theorem sub2398 (p : Pattern) : d13 (change p 112 (some 86)) = d13 p := by
  change (if p 159 then d2 (change p 112 (some 86)) else d10 (change p 112 (some 86))) = d13 p
  rw [sub2386, sub2395]
  rfl
theorem sub2399 (p : Pattern) : d14 (change p 112 (some 86)) = d14 p := by
  change (if p 158 then d13 (change p 112 (some 86)) else d12 (change p 112 (some 86))) = d14 p
  rw [sub2398, sub2397]
  rfl
end NetHack.Sokoban32Refined
