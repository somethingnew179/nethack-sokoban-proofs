/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions19
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2400 (p : Pattern) : d15 (change p 112 (some 86)) = d15 p := by
  change (if p 139 then d14 (change p 112 (some 86)) else d8 (change p 112 (some 86))) = d15 p
  rw [sub2399, sub2392]
  rfl
theorem sub2401 (p : Pattern) : d16 (change p 112 (some 86)) = d16 p := by
  change (if p 138 then d15 (change p 112 (some 86)) else d8 (change p 112 (some 86))) = d16 p
  rw [sub2400, sub2392]
  rfl
theorem sub2402 (p : Pattern) : d17 (change p 112 (some 86)) = d17 p := by
  change (if p 160 then d2 (change p 112 (some 86)) else d3 (change p 112 (some 86))) = d17 p
  rw [sub2386, sub2387]
  rfl
theorem sub2403 (p : Pattern) : d18 (change p 112 (some 86)) = d18 p := by
  change (if p 159 then d17 (change p 112 (some 86)) else d4 (change p 112 (some 86))) = d18 p
  rw [sub2402, sub2388]
  rfl
theorem sub2404 (p : Pattern) : d19 (change p 112 (some 86)) = d19 p := by
  change (if p 159 then d2 (change p 112 (some 86)) else d17 (change p 112 (some 86))) = d19 p
  rw [sub2386, sub2402]
  rfl
theorem sub2405 (p : Pattern) : d20 (change p 112 (some 86)) = d20 p := by
  change (if p 158 then d19 (change p 112 (some 86)) else d18 (change p 112 (some 86))) = d20 p
  rw [sub2404, sub2403]
  rfl
theorem sub2406 (p : Pattern) : d21 (change p 112 (some 86)) = d21 p := by
  change (if p 160 then d2 (change p 112 (some 86)) else d9 (change p 112 (some 86))) = d21 p
  rw [sub2386, sub2394]
  rfl
theorem sub2407 (p : Pattern) : d22 (change p 112 (some 86)) = d22 p := by
  change (if p 159 then d21 (change p 112 (some 86)) else d10 (change p 112 (some 86))) = d22 p
  rw [sub2406, sub2395]
  rfl
theorem sub2408 (p : Pattern) : d23 (change p 112 (some 86)) = d23 p := by
  change (if p 159 then d2 (change p 112 (some 86)) else d21 (change p 112 (some 86))) = d23 p
  rw [sub2386, sub2406]
  rfl
theorem sub2409 (p : Pattern) : d24 (change p 112 (some 86)) = d24 p := by
  change (if p 158 then d23 (change p 112 (some 86)) else d22 (change p 112 (some 86))) = d24 p
  rw [sub2408, sub2407]
  rfl
theorem sub2410 (p : Pattern) : d25 (change p 112 (some 86)) = d25 p := by
  change (if p 139 then d24 (change p 112 (some 86)) else d20 (change p 112 (some 86))) = d25 p
  rw [sub2409, sub2405]
  rfl
theorem sub2411 (p : Pattern) : d26 (change p 112 (some 86)) = d26 p := by
  change (if p 138 then d25 (change p 112 (some 86)) else d20 (change p 112 (some 86))) = d26 p
  rw [sub2410, sub2405]
  rfl
theorem sub2412 (p : Pattern) : d27 (change p 112 (some 86)) = d27 p := by
  change (if p 134 then d26 (change p 112 (some 86)) else d16 (change p 112 (some 86))) = d27 p
  rw [sub2411, sub2401]
  rfl
theorem sub2413 (p : Pattern) : d28 (change p 112 (some 86)) = d28 p := by
  change (if p 133 then d27 (change p 112 (some 86)) else d16 (change p 112 (some 86))) = d28 p
  rw [sub2412, sub2401]
  rfl
theorem sub2414 (p : Pattern) : d29 (change p 112 (some 86)) = d29 p := by
  change (if p 161 then d1 (change p 112 (some 86)) else d0 (change p 112 (some 86))) = d29 p
  rw [sub2393, sub2385]
  rfl
theorem sub2415 (p : Pattern) : d30 (change p 112 (some 86)) = d30 p := by
  change (if p 160 then d2 (change p 112 (some 86)) else d29 (change p 112 (some 86))) = d30 p
  rw [sub2386, sub2414]
  rfl
theorem sub2416 (p : Pattern) : d31 (change p 112 (some 86)) = d31 p := by
  change (if p 159 then d30 (change p 112 (some 86)) else d4 (change p 112 (some 86))) = d31 p
  rw [sub2415, sub2388]
  rfl
theorem sub2417 (p : Pattern) : d32 (change p 112 (some 86)) = d32 p := by
  change (if p 159 then d2 (change p 112 (some 86)) else d30 (change p 112 (some 86))) = d32 p
  rw [sub2386, sub2415]
  rfl
theorem sub2418 (p : Pattern) : d33 (change p 112 (some 86)) = d33 p := by
  change (if p 158 then d32 (change p 112 (some 86)) else d31 (change p 112 (some 86))) = d33 p
  rw [sub2417, sub2416]
  rfl
theorem sub2419 (p : Pattern) : d34 (change p 112 (some 86)) = d34 p := by
  change (if p 139 then d24 (change p 112 (some 86)) else d33 (change p 112 (some 86))) = d34 p
  rw [sub2409, sub2418]
  rfl
theorem sub2420 (p : Pattern) : d35 (change p 112 (some 86)) = d35 p := by
  change (if p 138 then d34 (change p 112 (some 86)) else d33 (change p 112 (some 86))) = d35 p
  rw [sub2419, sub2418]
  rfl
theorem sub2421 (p : Pattern) : d36 (change p 112 (some 86)) = d36 p := by
  change (if p 134 then d35 (change p 112 (some 86)) else d16 (change p 112 (some 86))) = d36 p
  rw [sub2420, sub2401]
  rfl
theorem sub2422 (p : Pattern) : d37 (change p 112 (some 86)) = d37 p := by
  change (if p 159 then d2 (change p 112 (some 86)) else d5 (change p 112 (some 86))) = d37 p
  rw [sub2386, sub2389]
  rfl
theorem sub2423 (p : Pattern) : d38 (change p 112 (some 86)) = d38 p := by
  change (if p 158 then d37 (change p 112 (some 86)) else d6 (change p 112 (some 86))) = d38 p
  rw [sub2422, sub2390]
  rfl
theorem sub2424 (p : Pattern) : d39 (change p 112 (some 86)) = d39 p := by
  change (if p 159 then d2 (change p 112 (some 86)) else d11 (change p 112 (some 86))) = d39 p
  rw [sub2386, sub2396]
  rfl
theorem sub2425 (p : Pattern) : d40 (change p 112 (some 86)) = d40 p := by
  change (if p 158 then d39 (change p 112 (some 86)) else d12 (change p 112 (some 86))) = d40 p
  rw [sub2424, sub2397]
  rfl
theorem sub2426 (p : Pattern) : d41 (change p 112 (some 86)) = d41 p := by
  change (if p 139 then d40 (change p 112 (some 86)) else d38 (change p 112 (some 86))) = d41 p
  rw [sub2425, sub2423]
  rfl
theorem sub2427 (p : Pattern) : d42 (change p 112 (some 86)) = d42 p := by
  change (if p 138 then d41 (change p 112 (some 86)) else d38 (change p 112 (some 86))) = d42 p
  rw [sub2426, sub2423]
  rfl
theorem sub2428 (p : Pattern) : d43 (change p 112 (some 86)) = d43 p := by
  change (if p 134 then d26 (change p 112 (some 86)) else d42 (change p 112 (some 86))) = d43 p
  rw [sub2411, sub2427]
  rfl
theorem sub2429 (p : Pattern) : d44 (change p 112 (some 86)) = d44 p := by
  change (if p 133 then d43 (change p 112 (some 86)) else d36 (change p 112 (some 86))) = d44 p
  rw [sub2428, sub2421]
  rfl
theorem sub2430 (p : Pattern) : d45 (change p 112 (some 86)) = d45 p := by
  change (if p 132 then d44 (change p 112 (some 86)) else d28 (change p 112 (some 86))) = d45 p
  rw [sub2429, sub2413]
  rfl
theorem sub2431 (p : Pattern) : d97 (change p 112 (some 86)) = d97 p := by
  change (if p 139 then d2 (change p 112 (some 86)) else d14 (change p 112 (some 86))) = d97 p
  rw [sub2386, sub2399]
  rfl
theorem sub2432 (p : Pattern) : d187 (change p 112 (some 86)) = d187 p := by
  change (if p 138 then d97 (change p 112 (some 86)) else d8 (change p 112 (some 86))) = d187 p
  rw [sub2431, sub2392]
  rfl
theorem sub2433 (p : Pattern) : d70 (change p 112 (some 86)) = d70 p := by
  change (if p 139 then d2 (change p 112 (some 86)) else d24 (change p 112 (some 86))) = d70 p
  rw [sub2386, sub2409]
  rfl
theorem sub2434 (p : Pattern) : d188 (change p 112 (some 86)) = d188 p := by
  change (if p 138 then d70 (change p 112 (some 86)) else d20 (change p 112 (some 86))) = d188 p
  rw [sub2433, sub2405]
  rfl
theorem sub2435 (p : Pattern) : d189 (change p 112 (some 86)) = d189 p := by
  change (if p 134 then d188 (change p 112 (some 86)) else d187 (change p 112 (some 86))) = d189 p
  rw [sub2434, sub2432]
  rfl
theorem sub2436 (p : Pattern) : d190 (change p 112 (some 86)) = d190 p := by
  change (if p 133 then d189 (change p 112 (some 86)) else d187 (change p 112 (some 86))) = d190 p
  rw [sub2435, sub2432]
  rfl
theorem sub2437 (p : Pattern) : d191 (change p 112 (some 86)) = d191 p := by
  change (if p 138 then d70 (change p 112 (some 86)) else d33 (change p 112 (some 86))) = d191 p
  rw [sub2433, sub2418]
  rfl
theorem sub2438 (p : Pattern) : d192 (change p 112 (some 86)) = d192 p := by
  change (if p 134 then d191 (change p 112 (some 86)) else d187 (change p 112 (some 86))) = d192 p
  rw [sub2437, sub2432]
  rfl
theorem sub2439 (p : Pattern) : d68 (change p 112 (some 86)) = d68 p := by
  change (if p 139 then d2 (change p 112 (some 86)) else d40 (change p 112 (some 86))) = d68 p
  rw [sub2386, sub2425]
  rfl
theorem sub2440 (p : Pattern) : d193 (change p 112 (some 86)) = d193 p := by
  change (if p 138 then d68 (change p 112 (some 86)) else d38 (change p 112 (some 86))) = d193 p
  rw [sub2439, sub2423]
  rfl
theorem sub2441 (p : Pattern) : d194 (change p 112 (some 86)) = d194 p := by
  change (if p 134 then d188 (change p 112 (some 86)) else d193 (change p 112 (some 86))) = d194 p
  rw [sub2434, sub2440]
  rfl
theorem sub2442 (p : Pattern) : d195 (change p 112 (some 86)) = d195 p := by
  change (if p 133 then d194 (change p 112 (some 86)) else d192 (change p 112 (some 86))) = d195 p
  rw [sub2441, sub2438]
  rfl
theorem sub2443 (p : Pattern) : d196 (change p 112 (some 86)) = d196 p := by
  change (if p 132 then d195 (change p 112 (some 86)) else d190 (change p 112 (some 86))) = d196 p
  rw [sub2442, sub2436]
  rfl
theorem sub2444 (p : Pattern) : d197 (change p 112 (some 86)) = d197 p := by
  change (if p 113 then d196 (change p 112 (some 86)) else d45 (change p 112 (some 86))) = d197 p
  rw [sub2443, sub2430]
  rfl
theorem sub2445 (p : Pattern) : d198 (change p 112 (some 86)) = d197 p := by
  change d197 (change p 112 (some 86)) = d197 p
  exact sub2444 p
theorem sub2446 (p : Pattern) : d75 (change p 112 (some 86)) = d75 p := by
  change (if p 134 then d70 (change p 112 (some 86)) else d68 (change p 112 (some 86))) = d75 p
  rw [sub2433, sub2439]
  rfl
theorem sub2447 (p : Pattern) : d76 (change p 112 (some 86)) = d76 p := by
  change (if p 133 then d75 (change p 112 (some 86)) else d27 (change p 112 (some 86))) = d76 p
  rw [sub2446, sub2412]
  rfl
theorem sub2448 (p : Pattern) : d77 (change p 112 (some 86)) = d77 p := by
  change (if p 132 then d76 (change p 112 (some 86)) else d28 (change p 112 (some 86))) = d77 p
  rw [sub2447, sub2413]
  rfl
theorem sub2449 (p : Pattern) : d199 (change p 112 (some 86)) = d199 p := by
  change (if p 138 then d2 (change p 112 (some 86)) else d68 (change p 112 (some 86))) = d199 p
  rw [sub2386, sub2439]
  rfl
theorem sub2450 (p : Pattern) : d200 (change p 112 (some 86)) = d200 p := by
  change (if p 138 then d2 (change p 112 (some 86)) else d70 (change p 112 (some 86))) = d200 p
  rw [sub2386, sub2433]
  rfl
theorem sub2451 (p : Pattern) : d201 (change p 112 (some 86)) = d201 p := by
  change (if p 134 then d200 (change p 112 (some 86)) else d199 (change p 112 (some 86))) = d201 p
  rw [sub2450, sub2449]
  rfl
theorem sub2452 (p : Pattern) : d202 (change p 112 (some 86)) = d202 p := by
  change (if p 133 then d201 (change p 112 (some 86)) else d189 (change p 112 (some 86))) = d202 p
  rw [sub2451, sub2435]
  rfl
theorem sub2453 (p : Pattern) : d203 (change p 112 (some 86)) = d203 p := by
  change (if p 132 then d202 (change p 112 (some 86)) else d190 (change p 112 (some 86))) = d203 p
  rw [sub2452, sub2436]
  rfl
theorem sub2454 (p : Pattern) : d204 (change p 112 (some 86)) = d204 p := by
  change (if p 113 then d203 (change p 112 (some 86)) else d77 (change p 112 (some 86))) = d204 p
  rw [sub2453, sub2448]
  rfl
theorem sub2455 (p : Pattern) : d205 (change p 112 (some 86)) = d204 p := by
  change d204 (change p 112 (some 86)) = d204 p
  exact sub2454 p
theorem sub2456 (p : Pattern) : d206 (change p 112 (some 86)) = d1386 p := by
  change (if p 106 then d205 (change p 112 (some 86)) else d198 (change p 112 (some 86))) = d1386 p
  rw [sub2455, sub2445]
  rfl
theorem sub2457 (p : Pattern) : d207 (change p 112 (some 86)) = d1386 p := by
  change d206 (change p 112 (some 86)) = d1386 p
  exact sub2456 p
theorem sub2458 (p : Pattern) : d119 (change p 112 (some 86)) = d119 p := by
  change (if p 139 then d20 (change p 112 (some 86)) else d33 (change p 112 (some 86))) = d119 p
  rw [sub2405, sub2418]
  rfl
theorem sub2459 (p : Pattern) : d211 (change p 112 (some 86)) = d211 p := by
  change (if p 138 then d70 (change p 112 (some 86)) else d119 (change p 112 (some 86))) = d211 p
  rw [sub2433, sub2458]
  rfl
theorem sub2460 (p : Pattern) : d212 (change p 112 (some 86)) = d212 p := by
  change (if p 134 then d211 (change p 112 (some 86)) else d187 (change p 112 (some 86))) = d212 p
  rw [sub2459, sub2432]
  rfl
theorem sub2461 (p : Pattern) : d213 (change p 112 (some 86)) = d213 p := by
  change (if p 133 then d194 (change p 112 (some 86)) else d212 (change p 112 (some 86))) = d213 p
  rw [sub2441, sub2460]
  rfl
theorem sub2462 (p : Pattern) : d214 (change p 112 (some 86)) = d214 p := by
  change (if p 132 then d213 (change p 112 (some 86)) else d190 (change p 112 (some 86))) = d214 p
  rw [sub2461, sub2436]
  rfl
theorem sub2463 (p : Pattern) : d215 (change p 112 (some 86)) = d215 p := by
  change (if p 113 then d214 (change p 112 (some 86)) else d45 (change p 112 (some 86))) = d215 p
  rw [sub2462, sub2430]
  rfl
theorem sub2464 (p : Pattern) : d216 (change p 112 (some 86)) = d215 p := by
  change d215 (change p 112 (some 86)) = d215 p
  exact sub2463 p
theorem sub2465 (p : Pattern) : d217 (change p 112 (some 86)) = d217 p := by
  change (if p 138 then d97 (change p 112 (some 86)) else d15 (change p 112 (some 86))) = d217 p
  rw [sub2431, sub2400]
  rfl
theorem sub2466 (p : Pattern) : d218 (change p 112 (some 86)) = d218 p := by
  change (if p 138 then d70 (change p 112 (some 86)) else d25 (change p 112 (some 86))) = d218 p
  rw [sub2433, sub2410]
  rfl
theorem sub2467 (p : Pattern) : d219 (change p 112 (some 86)) = d219 p := by
  change (if p 134 then d218 (change p 112 (some 86)) else d217 (change p 112 (some 86))) = d219 p
  rw [sub2466, sub2465]
  rfl
theorem sub2468 (p : Pattern) : d220 (change p 112 (some 86)) = d220 p := by
  change (if p 133 then d219 (change p 112 (some 86)) else d217 (change p 112 (some 86))) = d220 p
  rw [sub2467, sub2465]
  rfl
theorem sub2469 (p : Pattern) : d221 (change p 112 (some 86)) = d221 p := by
  change (if p 133 then d201 (change p 112 (some 86)) else d219 (change p 112 (some 86))) = d221 p
  rw [sub2451, sub2467]
  rfl
theorem sub2470 (p : Pattern) : d222 (change p 112 (some 86)) = d222 p := by
  change (if p 132 then d221 (change p 112 (some 86)) else d220 (change p 112 (some 86))) = d222 p
  rw [sub2469, sub2468]
  rfl
theorem sub2471 (p : Pattern) : d223 (change p 112 (some 86)) = d223 p := by
  change (if p 113 then d222 (change p 112 (some 86)) else d77 (change p 112 (some 86))) = d223 p
  rw [sub2470, sub2448]
  rfl
theorem sub2472 (p : Pattern) : d224 (change p 112 (some 86)) = d223 p := by
  change d223 (change p 112 (some 86)) = d223 p
  exact sub2471 p
theorem sub2473 (p : Pattern) : d225 (change p 112 (some 86)) = d1387 p := by
  change (if p 106 then d224 (change p 112 (some 86)) else d216 (change p 112 (some 86))) = d1387 p
  rw [sub2472, sub2464]
  rfl
theorem sub2474 (p : Pattern) : d226 (change p 112 (some 86)) = d1387 p := by
  change d225 (change p 112 (some 86)) = d1387 p
  exact sub2473 p
theorem sub2475 (p : Pattern) : d227 (change p 112 (some 86)) = d1388 p := by
  change (if p 80 then d226 (change p 112 (some 86)) else d207 (change p 112 (some 86))) = d1388 p
  rw [sub2474, sub2457]
  rfl
theorem sub2476 (p : Pattern) : d0 (change p 138 none) = d0 p := by
  rfl
theorem sub2477 (p : Pattern) : d2 (change p 138 none) = d2 p := by
  rfl
theorem sub2478 (p : Pattern) : d3 (change p 138 none) = d3 p := by
  change (if p 161 then d2 (change p 138 none) else d0 (change p 138 none)) = d3 p
  rw [sub2477, sub2476]
  rfl
theorem sub2479 (p : Pattern) : d4 (change p 138 none) = d4 p := by
  change (if p 160 then d3 (change p 138 none) else d0 (change p 138 none)) = d4 p
  rw [sub2478, sub2476]
  rfl
theorem sub2480 (p : Pattern) : d5 (change p 138 none) = d5 p := by
  change (if p 160 then d2 (change p 138 none) else d0 (change p 138 none)) = d5 p
  rw [sub2477, sub2476]
  rfl
theorem sub2481 (p : Pattern) : d6 (change p 138 none) = d6 p := by
  change (if p 159 then d5 (change p 138 none) else d4 (change p 138 none)) = d6 p
  rw [sub2480, sub2479]
  rfl
theorem sub2482 (p : Pattern) : d7 (change p 138 none) = d7 p := by
  change (if p 159 then d2 (change p 138 none) else d4 (change p 138 none)) = d7 p
  rw [sub2477, sub2479]
  rfl
theorem sub2483 (p : Pattern) : d8 (change p 138 none) = d8 p := by
  change (if p 158 then d7 (change p 138 none) else d6 (change p 138 none)) = d8 p
  rw [sub2482, sub2481]
  rfl
theorem sub2484 (p : Pattern) : d389 (change p 138 none) = d8 p := by
  change d8 (change p 138 none) = d8 p
  exact sub2483 p
theorem sub2485 (p : Pattern) : d17 (change p 138 none) = d17 p := by
  change (if p 160 then d2 (change p 138 none) else d3 (change p 138 none)) = d17 p
  rw [sub2477, sub2478]
  rfl
theorem sub2486 (p : Pattern) : d18 (change p 138 none) = d18 p := by
  change (if p 159 then d17 (change p 138 none) else d4 (change p 138 none)) = d18 p
  rw [sub2485, sub2479]
  rfl
theorem sub2487 (p : Pattern) : d19 (change p 138 none) = d19 p := by
  change (if p 159 then d2 (change p 138 none) else d17 (change p 138 none)) = d19 p
  rw [sub2477, sub2485]
  rfl
theorem sub2488 (p : Pattern) : d20 (change p 138 none) = d20 p := by
  change (if p 158 then d19 (change p 138 none) else d18 (change p 138 none)) = d20 p
  rw [sub2487, sub2486]
  rfl
theorem sub2489 (p : Pattern) : d390 (change p 138 none) = d20 p := by
  change d20 (change p 138 none) = d20 p
  exact sub2488 p
theorem sub2490 (p : Pattern) : d391 (change p 138 none) = d1097 p := by
  change (if p 134 then d390 (change p 138 none) else d389 (change p 138 none)) = d1097 p
  rw [sub2489, sub2484]
  rfl
theorem sub2491 (p : Pattern) : d392 (change p 138 none) = d1098 p := by
  change (if p 133 then d391 (change p 138 none) else d389 (change p 138 none)) = d1098 p
  rw [sub2490, sub2484]
  rfl
theorem sub2492 (p : Pattern) : d1 (change p 138 none) = d1 p := by
  rfl
theorem sub2493 (p : Pattern) : d29 (change p 138 none) = d29 p := by
  change (if p 161 then d1 (change p 138 none) else d0 (change p 138 none)) = d29 p
  rw [sub2492, sub2476]
  rfl
theorem sub2494 (p : Pattern) : d30 (change p 138 none) = d30 p := by
  change (if p 160 then d2 (change p 138 none) else d29 (change p 138 none)) = d30 p
  rw [sub2477, sub2493]
  rfl
theorem sub2495 (p : Pattern) : d31 (change p 138 none) = d31 p := by
  change (if p 159 then d30 (change p 138 none) else d4 (change p 138 none)) = d31 p
  rw [sub2494, sub2479]
  rfl
theorem sub2496 (p : Pattern) : d32 (change p 138 none) = d32 p := by
  change (if p 159 then d2 (change p 138 none) else d30 (change p 138 none)) = d32 p
  rw [sub2477, sub2494]
  rfl
theorem sub2497 (p : Pattern) : d33 (change p 138 none) = d33 p := by
  change (if p 158 then d32 (change p 138 none) else d31 (change p 138 none)) = d33 p
  rw [sub2496, sub2495]
  rfl
theorem sub2498 (p : Pattern) : d393 (change p 138 none) = d33 p := by
  change d33 (change p 138 none) = d33 p
  exact sub2497 p
theorem sub2499 (p : Pattern) : d394 (change p 138 none) = d1099 p := by
  change (if p 134 then d393 (change p 138 none) else d389 (change p 138 none)) = d1099 p
  rw [sub2498, sub2484]
  rfl
theorem sub2500 (p : Pattern) : d37 (change p 138 none) = d37 p := by
  change (if p 159 then d2 (change p 138 none) else d5 (change p 138 none)) = d37 p
  rw [sub2477, sub2480]
  rfl
theorem sub2501 (p : Pattern) : d38 (change p 138 none) = d38 p := by
  change (if p 158 then d37 (change p 138 none) else d6 (change p 138 none)) = d38 p
  rw [sub2500, sub2481]
  rfl
theorem sub2502 (p : Pattern) : d395 (change p 138 none) = d38 p := by
  change d38 (change p 138 none) = d38 p
  exact sub2501 p
theorem sub2503 (p : Pattern) : d396 (change p 138 none) = d1100 p := by
  change (if p 134 then d390 (change p 138 none) else d395 (change p 138 none)) = d1100 p
  rw [sub2489, sub2502]
  rfl
theorem sub2504 (p : Pattern) : d397 (change p 138 none) = d1101 p := by
  change (if p 133 then d396 (change p 138 none) else d394 (change p 138 none)) = d1101 p
  rw [sub2503, sub2499]
  rfl
theorem sub2505 (p : Pattern) : d398 (change p 138 none) = d1102 p := by
  change (if p 132 then d397 (change p 138 none) else d392 (change p 138 none)) = d1102 p
  rw [sub2504, sub2491]
  rfl
theorem sub2506 (p : Pattern) : d9 (change p 138 none) = d9 p := by
  change (if p 161 then d2 (change p 138 none) else d1 (change p 138 none)) = d9 p
  rw [sub2477, sub2492]
  rfl
theorem sub2507 (p : Pattern) : d10 (change p 138 none) = d10 p := by
  change (if p 160 then d9 (change p 138 none) else d1 (change p 138 none)) = d10 p
  rw [sub2506, sub2492]
  rfl
theorem sub2508 (p : Pattern) : d11 (change p 138 none) = d11 p := by
  change (if p 160 then d2 (change p 138 none) else d1 (change p 138 none)) = d11 p
  rw [sub2477, sub2492]
  rfl
theorem sub2509 (p : Pattern) : d12 (change p 138 none) = d12 p := by
  change (if p 159 then d11 (change p 138 none) else d10 (change p 138 none)) = d12 p
  rw [sub2508, sub2507]
  rfl
theorem sub2510 (p : Pattern) : d13 (change p 138 none) = d13 p := by
  change (if p 159 then d2 (change p 138 none) else d10 (change p 138 none)) = d13 p
  rw [sub2477, sub2507]
  rfl
theorem sub2511 (p : Pattern) : d14 (change p 138 none) = d14 p := by
  change (if p 158 then d13 (change p 138 none) else d12 (change p 138 none)) = d14 p
  rw [sub2510, sub2509]
  rfl
theorem sub2512 (p : Pattern) : d15 (change p 138 none) = d15 p := by
  change (if p 139 then d14 (change p 138 none) else d8 (change p 138 none)) = d15 p
  rw [sub2511, sub2483]
  rfl
theorem sub2513 (p : Pattern) : d399 (change p 138 none) = d15 p := by
  change d15 (change p 138 none) = d15 p
  exact sub2512 p
theorem sub2514 (p : Pattern) : d21 (change p 138 none) = d21 p := by
  change (if p 160 then d2 (change p 138 none) else d9 (change p 138 none)) = d21 p
  rw [sub2477, sub2506]
  rfl
theorem sub2515 (p : Pattern) : d22 (change p 138 none) = d22 p := by
  change (if p 159 then d21 (change p 138 none) else d10 (change p 138 none)) = d22 p
  rw [sub2514, sub2507]
  rfl
theorem sub2516 (p : Pattern) : d23 (change p 138 none) = d23 p := by
  change (if p 159 then d2 (change p 138 none) else d21 (change p 138 none)) = d23 p
  rw [sub2477, sub2514]
  rfl
theorem sub2517 (p : Pattern) : d24 (change p 138 none) = d24 p := by
  change (if p 158 then d23 (change p 138 none) else d22 (change p 138 none)) = d24 p
  rw [sub2516, sub2515]
  rfl
theorem sub2518 (p : Pattern) : d25 (change p 138 none) = d25 p := by
  change (if p 139 then d24 (change p 138 none) else d20 (change p 138 none)) = d25 p
  rw [sub2517, sub2488]
  rfl
theorem sub2519 (p : Pattern) : d400 (change p 138 none) = d25 p := by
  change d25 (change p 138 none) = d25 p
  exact sub2518 p
end NetHack.Sokoban32Refined
