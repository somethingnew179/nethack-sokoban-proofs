/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions15
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s2400 (pattern : Twelve) : d1278 (change pattern 9 8) = d872 pattern := by
  change d872 (change pattern 9 8) = d872 pattern
  exact s2399 pattern
theorem s2401 (pattern : Twelve) : d1284 (change pattern 9 8) = d872 pattern := by
  change (if pattern.h then d872 (change pattern 9 8) else d1278 (change pattern 9 8)) = d872 pattern
  rw [s2399, s2400]
  simp only [ite_self]
theorem s2402 (pattern : Twelve) : d1293 (change pattern 9 8) = d1976 pattern := by
  change (if pattern.f then d1284 (change pattern 9 8) else d17 (change pattern 9 8)) = d1976 pattern
  rw [s2401, s2373]
  rfl
theorem s2403 (pattern : Twelve) : d10 (change pattern 9 8) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 9 8) else d0 (change pattern 9 8)) = d10 pattern
  rw [s2336, s2330]
  rfl
theorem s2404 (pattern : Twelve) : d11 (change pattern 9 8) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 9 8) else d1 (change pattern 9 8)) = d11 pattern
  rw [s2338, s2331]
  rfl
theorem s2405 (pattern : Twelve) : d19 (change pattern 9 8) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 9 8) else d10 (change pattern 9 8)) = d19 pattern
  rw [s2404, s2403]
  rfl
theorem s2406 (pattern : Twelve) : d1294 (change pattern 9 8) = d1294 pattern := by
  change (if pattern.f then d6 (change pattern 9 8) else d19 (change pattern 9 8)) = d1294 pattern
  rw [s2342, s2405]
  rfl
theorem s2407 (pattern : Twelve) : d1305 (change pattern 9 8) = d1977 pattern := by
  change (if pattern.e then d1294 (change pattern 9 8) else d1293 (change pattern 9 8)) = d1977 pattern
  rw [s2406, s2402]
  rfl
theorem s2408 (pattern : Twelve) : d1435 (change pattern 9 8) = d1977 pattern := by
  change d1305 (change pattern 9 8) = d1977 pattern
  exact s2407 pattern
theorem s2409 (pattern : Twelve) : d1436 (change pattern 9 8) = d1977 pattern := by
  change d1305 (change pattern 9 8) = d1977 pattern
  exact s2407 pattern
theorem s2410 (pattern : Twelve) : d1438 (change pattern 9 8) = d1977 pattern := by
  change (if pattern.d then d1436 (change pattern 9 8) else d1435 (change pattern 9 8)) = d1977 pattern
  rw [s2409, s2408]
  simp only [ite_self]
theorem s2411 (pattern : Twelve) : d1439 (change pattern 9 8) = d1977 pattern := by
  change (if pattern.c then d1436 (change pattern 9 8) else d1438 (change pattern 9 8)) = d1977 pattern
  rw [s2409, s2410]
  simp only [ite_self]
theorem s2412 (pattern : Twelve) : d1283 (change pattern 9 8) = d23 pattern := by
  change d23 (change pattern 9 8) = d23 pattern
  exact s2348 pattern
theorem s2413 (pattern : Twelve) : d1301 (change pattern 9 8) = d1987 pattern := by
  change (if pattern.f then d6 (change pattern 9 8) else d1283 (change pattern 9 8)) = d1987 pattern
  rw [s2342, s2412]
  rfl
theorem s2414 (pattern : Twelve) : d1309 (change pattern 9 8) = d1988 pattern := by
  change (if pattern.e then d1301 (change pattern 9 8) else d1293 (change pattern 9 8)) = d1988 pattern
  rw [s2413, s2402]
  rfl
theorem s2415 (pattern : Twelve) : d1437 (change pattern 9 8) = d1988 pattern := by
  change d1309 (change pattern 9 8) = d1988 pattern
  exact s2414 pattern
theorem s2416 (pattern : Twelve) : d1440 (change pattern 9 8) = d2296 pattern := by
  change (if pattern.g then d1437 (change pattern 9 8) else d1439 (change pattern 9 8)) = d2296 pattern
  rw [s2415, s2411]
  rfl
theorem s2417 (pattern : Twelve) : d1441 (change pattern 9 8) = d2296 pattern := by
  change (if pattern.g then d1437 (change pattern 9 8) else d1436 (change pattern 9 8)) = d2296 pattern
  rw [s2415, s2409]
  rfl
theorem s2418 (pattern : Twelve) : d1442 (change pattern 9 8) = d2296 pattern := by
  change (if pattern.b then d1441 (change pattern 9 8) else d1440 (change pattern 9 8)) = d2296 pattern
  rw [s2417, s2416]
  simp only [ite_self]
theorem s2419 (pattern : Twelve) : d1443 (change pattern 9 8) = d2296 pattern := by
  change (if pattern.a then d1441 (change pattern 9 8) else d1442 (change pattern 9 8)) = d2296 pattern
  rw [s2417, s2418]
  simp only [ite_self]
theorem s2420 (pattern : Twelve) : d1324 (change pattern 9 8) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 9 8) else d11 (change pattern 9 8)) = d1324 pattern
  rw [s2375, s2404]
  rfl
theorem s2421 (pattern : Twelve) : d1649 (change pattern 9 8) = d1649 pattern := by
  change (if pattern.f then d1324 (change pattern 9 8) else d19 (change pattern 9 8)) = d1649 pattern
  rw [s2420, s2405]
  rfl
theorem s2422 (pattern : Twelve) : d1650 (change pattern 9 8) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 9 8) else d25 (change pattern 9 8)) = d1650 pattern
  rw [s2342, s2378]
  rfl
theorem s2423 (pattern : Twelve) : d1656 (change pattern 9 8) = d1656 pattern := by
  change (if pattern.e then d1650 (change pattern 9 8) else d1649 (change pattern 9 8)) = d1656 pattern
  rw [s2422, s2421]
  rfl
theorem s2424 (pattern : Twelve) : d1715 (change pattern 9 8) = d1656 pattern := by
  change d1656 (change pattern 9 8) = d1656 pattern
  exact s2423 pattern
theorem s2425 (pattern : Twelve) : d0 (change pattern 9 2) = d0 pattern := by
  rfl
theorem s2426 (pattern : Twelve) : d1 (change pattern 9 2) = d1 pattern := by
  rfl
theorem s2427 (pattern : Twelve) : d26 (change pattern 9 2) = d26 pattern := by
  change (if pattern.i then d1 (change pattern 9 2) else d0 (change pattern 9 2)) = d26 pattern
  rw [s2426, s2425]
  rfl
theorem s2428 (pattern : Twelve) : d7 (change pattern 9 2) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 9 2) else d0 (change pattern 9 2)) = d7 pattern
  rw [s2426, s2425]
  rfl
theorem s2429 (pattern : Twelve) : d17 (change pattern 9 2) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 9 2) else d0 (change pattern 9 2)) = d17 pattern
  rw [s2428, s2425]
  rfl
theorem s2430 (pattern : Twelve) : d27 (change pattern 9 2) = d27 pattern := by
  change (if pattern.i then d1 (change pattern 9 2) else d17 (change pattern 9 2)) = d27 pattern
  rw [s2426, s2429]
  rfl
theorem s2431 (pattern : Twelve) : d50 (change pattern 9 2) = d50 pattern := by
  change (if pattern.h then d27 (change pattern 9 2) else d26 (change pattern 9 2)) = d50 pattern
  rw [s2430, s2427]
  rfl
theorem s2432 (pattern : Twelve) : d72 (change pattern 9 2) = d72 pattern := by
  change (if pattern.f then d50 (change pattern 9 2) else d0 (change pattern 9 2)) = d72 pattern
  rw [s2431, s2425]
  rfl
theorem s2433 (pattern : Twelve) : d2 (change pattern 9 2) = d2 pattern := by
  rfl
theorem s2434 (pattern : Twelve) : d8 (change pattern 9 2) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 9 2) else d1 (change pattern 9 2)) = d8 pattern
  rw [s2433, s2426]
  rfl
theorem s2435 (pattern : Twelve) : d3 (change pattern 9 2) = d3 pattern := by
  rfl
theorem s2436 (pattern : Twelve) : d9 (change pattern 9 2) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 9 2) else d2 (change pattern 9 2)) = d9 pattern
  rw [s2435, s2433]
  rfl
theorem s2437 (pattern : Twelve) : d18 (change pattern 9 2) = d18 pattern := by
  change (if pattern.k then d9 (change pattern 9 2) else d8 (change pattern 9 2)) = d18 pattern
  rw [s2436, s2434]
  rfl
theorem s2438 (pattern : Twelve) : d28 (change pattern 9 2) = d28 pattern := by
  change (if pattern.i then d18 (change pattern 9 2) else d17 (change pattern 9 2)) = d28 pattern
  rw [s2437, s2429]
  rfl
theorem s2439 (pattern : Twelve) : d10 (change pattern 9 2) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 9 2) else d0 (change pattern 9 2)) = d10 pattern
  rw [s2433, s2425]
  rfl
theorem s2440 (pattern : Twelve) : d11 (change pattern 9 2) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 9 2) else d1 (change pattern 9 2)) = d11 pattern
  rw [s2435, s2426]
  rfl
theorem s2441 (pattern : Twelve) : d19 (change pattern 9 2) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 9 2) else d10 (change pattern 9 2)) = d19 pattern
  rw [s2440, s2439]
  rfl
theorem s2442 (pattern : Twelve) : d6 (change pattern 9 2) = d6 pattern := by
  rfl
theorem s2443 (pattern : Twelve) : d29 (change pattern 9 2) = d29 pattern := by
  change (if pattern.i then d6 (change pattern 9 2) else d19 (change pattern 9 2)) = d29 pattern
  rw [s2442, s2441]
  rfl
theorem s2444 (pattern : Twelve) : d51 (change pattern 9 2) = d51 pattern := by
  change (if pattern.h then d29 (change pattern 9 2) else d28 (change pattern 9 2)) = d51 pattern
  rw [s2443, s2438]
  rfl
theorem s2445 (pattern : Twelve) : d73 (change pattern 9 2) = d73 pattern := by
  change (if pattern.f then d51 (change pattern 9 2) else d0 (change pattern 9 2)) = d73 pattern
  rw [s2444, s2425]
  rfl
theorem s2446 (pattern : Twelve) : d91 (change pattern 9 2) = d91 pattern := by
  change (if pattern.e then d73 (change pattern 9 2) else d72 (change pattern 9 2)) = d91 pattern
  rw [s2445, s2432]
  rfl
theorem s2447 (pattern : Twelve) : d354 (change pattern 9 2) = d91 pattern := by
  change d91 (change pattern 9 2) = d91 pattern
  exact s2446 pattern
theorem s2448 (pattern : Twelve) : d23 (change pattern 9 2) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 9 2) else d2 (change pattern 9 2)) = d23 pattern
  rw [s2436, s2433]
  rfl
theorem s2449 (pattern : Twelve) : d34 (change pattern 9 2) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 9 2) else d17 (change pattern 9 2)) = d34 pattern
  rw [s2448, s2429]
  rfl
theorem s2450 (pattern : Twelve) : d55 (change pattern 9 2) = d55 pattern := by
  change (if pattern.h then d29 (change pattern 9 2) else d34 (change pattern 9 2)) = d55 pattern
  rw [s2443, s2449]
  rfl
theorem s2451 (pattern : Twelve) : d76 (change pattern 9 2) = d76 pattern := by
  change (if pattern.f then d55 (change pattern 9 2) else d0 (change pattern 9 2)) = d76 pattern
  rw [s2450, s2425]
  rfl
theorem s2452 (pattern : Twelve) : d93 (change pattern 9 2) = d93 pattern := by
  change (if pattern.e then d76 (change pattern 9 2) else d72 (change pattern 9 2)) = d93 pattern
  rw [s2451, s2432]
  rfl
theorem s2453 (pattern : Twelve) : d355 (change pattern 9 2) = d93 pattern := by
  change d93 (change pattern 9 2) = d93 pattern
  exact s2452 pattern
theorem s2454 (pattern : Twelve) : d359 (change pattern 9 2) = d2297 pattern := by
  change (if pattern.d then d355 (change pattern 9 2) else d354 (change pattern 9 2)) = d2297 pattern
  rw [s2453, s2447]
  rfl
theorem s2455 (pattern : Twelve) : d361 (change pattern 9 2) = d2297 pattern := by
  change d359 (change pattern 9 2) = d2297 pattern
  exact s2454 pattern
theorem s2456 (pattern : Twelve) : d30 (change pattern 9 2) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 9 2) else d0 (change pattern 9 2)) = d30 pattern
  rw [s2433, s2425]
  rfl
theorem s2457 (pattern : Twelve) : d80 (change pattern 9 2) = d80 pattern := by
  change (if pattern.f then d55 (change pattern 9 2) else d30 (change pattern 9 2)) = d80 pattern
  rw [s2450, s2456]
  rfl
theorem s2458 (pattern : Twelve) : d97 (change pattern 9 2) = d97 pattern := by
  change (if pattern.e then d80 (change pattern 9 2) else d72 (change pattern 9 2)) = d97 pattern
  rw [s2457, s2432]
  rfl
theorem s2459 (pattern : Twelve) : d356 (change pattern 9 2) = d97 pattern := by
  change d97 (change pattern 9 2) = d97 pattern
  exact s2458 pattern
theorem s2460 (pattern : Twelve) : d362 (change pattern 9 2) = d2298 pattern := by
  change (if pattern.g then d356 (change pattern 9 2) else d361 (change pattern 9 2)) = d2298 pattern
  rw [s2459, s2455]
  rfl
theorem s2461 (pattern : Twelve) : d357 (change pattern 9 2) = d91 pattern := by
  change d91 (change pattern 9 2) = d91 pattern
  exact s2446 pattern
theorem s2462 (pattern : Twelve) : d360 (change pattern 9 2) = d2297 pattern := by
  change (if pattern.d then d355 (change pattern 9 2) else d357 (change pattern 9 2)) = d2297 pattern
  rw [s2453, s2461]
  rfl
theorem s2463 (pattern : Twelve) : d363 (change pattern 9 2) = d2298 pattern := by
  change (if pattern.g then d356 (change pattern 9 2) else d360 (change pattern 9 2)) = d2298 pattern
  rw [s2459, s2462]
  rfl
theorem s2464 (pattern : Twelve) : d364 (change pattern 9 2) = d2298 pattern := by
  change (if pattern.b then d363 (change pattern 9 2) else d362 (change pattern 9 2)) = d2298 pattern
  rw [s2463, s2460]
  simp only [ite_self]
theorem s2465 (pattern : Twelve) : d365 (change pattern 9 2) = d2298 pattern := by
  change (if pattern.a then d363 (change pattern 9 2) else d364 (change pattern 9 2)) = d2298 pattern
  rw [s2463, s2464]
  simp only [ite_self]
theorem s2466 (pattern : Twelve) : d814 (change pattern 9 2) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 9 2) else d7 (change pattern 9 2)) = d814 pattern
  rw [s2426, s2428]
  rfl
theorem s2467 (pattern : Twelve) : d816 (change pattern 9 2) = d816 pattern := by
  change (if pattern.i then d1 (change pattern 9 2) else d814 (change pattern 9 2)) = d816 pattern
  rw [s2426, s2466]
  rfl
theorem s2468 (pattern : Twelve) : d824 (change pattern 9 2) = d824 pattern := by
  change (if pattern.h then d816 (change pattern 9 2) else d27 (change pattern 9 2)) = d824 pattern
  rw [s2467, s2430]
  rfl
theorem s2469 (pattern : Twelve) : d838 (change pattern 9 2) = d838 pattern := by
  change (if pattern.f then d824 (change pattern 9 2) else d0 (change pattern 9 2)) = d838 pattern
  rw [s2468, s2425]
  rfl
theorem s2470 (pattern : Twelve) : d4 (change pattern 9 2) = d4 pattern := by
  rfl
theorem s2471 (pattern : Twelve) : d16 (change pattern 9 2) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 9 2) else d2 (change pattern 9 2)) = d16 pattern
  rw [s2470, s2433]
  rfl
theorem s2472 (pattern : Twelve) : d5 (change pattern 9 2) = d5 pattern := by
  rfl
theorem s2473 (pattern : Twelve) : d12 (change pattern 9 2) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 9 2) else d3 (change pattern 9 2)) = d12 pattern
  rw [s2472, s2435]
  rfl
theorem s2474 (pattern : Twelve) : d25 (change pattern 9 2) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 9 2) else d16 (change pattern 9 2)) = d25 pattern
  rw [s2473, s2471]
  rfl
theorem s2475 (pattern : Twelve) : d817 (change pattern 9 2) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 9 2) else d19 (change pattern 9 2)) = d817 pattern
  rw [s2474, s2441]
  rfl
theorem s2476 (pattern : Twelve) : d42 (change pattern 9 2) = d42 pattern := by
  change (if pattern.i then d6 (change pattern 9 2) else d25 (change pattern 9 2)) = d42 pattern
  rw [s2442, s2474]
  rfl
theorem s2477 (pattern : Twelve) : d825 (change pattern 9 2) = d825 pattern := by
  change (if pattern.h then d42 (change pattern 9 2) else d817 (change pattern 9 2)) = d825 pattern
  rw [s2476, s2475]
  rfl
theorem s2478 (pattern : Twelve) : d839 (change pattern 9 2) = d839 pattern := by
  change (if pattern.f then d825 (change pattern 9 2) else d17 (change pattern 9 2)) = d839 pattern
  rw [s2477, s2429]
  rfl
theorem s2479 (pattern : Twelve) : d853 (change pattern 9 2) = d853 pattern := by
  change (if pattern.e then d839 (change pattern 9 2) else d838 (change pattern 9 2)) = d853 pattern
  rw [s2478, s2469]
  rfl
theorem s2480 (pattern : Twelve) : d1020 (change pattern 9 2) = d853 pattern := by
  change d853 (change pattern 9 2) = d853 pattern
  exact s2479 pattern
theorem s2481 (pattern : Twelve) : d1021 (change pattern 9 2) = d853 pattern := by
  change d853 (change pattern 9 2) = d853 pattern
  exact s2479 pattern
theorem s2482 (pattern : Twelve) : d1024 (change pattern 9 2) = d853 pattern := by
  change (if pattern.d then d1021 (change pattern 9 2) else d1020 (change pattern 9 2)) = d853 pattern
  rw [s2481, s2480]
  simp only [ite_self]
theorem s2483 (pattern : Twelve) : d1025 (change pattern 9 2) = d853 pattern := by
  change d1024 (change pattern 9 2) = d853 pattern
  exact s2482 pattern
theorem s2484 (pattern : Twelve) : d823 (change pattern 9 2) = d823 pattern := by
  change (if pattern.i then d2 (change pattern 9 2) else d17 (change pattern 9 2)) = d823 pattern
  rw [s2433, s2429]
  rfl
theorem s2485 (pattern : Twelve) : d846 (change pattern 9 2) = d846 pattern := by
  change (if pattern.f then d825 (change pattern 9 2) else d823 (change pattern 9 2)) = d846 pattern
  rw [s2477, s2484]
  rfl
theorem s2486 (pattern : Twelve) : d857 (change pattern 9 2) = d857 pattern := by
  change (if pattern.e then d846 (change pattern 9 2) else d838 (change pattern 9 2)) = d857 pattern
  rw [s2485, s2469]
  rfl
theorem s2487 (pattern : Twelve) : d1022 (change pattern 9 2) = d857 pattern := by
  change d857 (change pattern 9 2) = d857 pattern
  exact s2486 pattern
theorem s2488 (pattern : Twelve) : d1026 (change pattern 9 2) = d2299 pattern := by
  change (if pattern.g then d1022 (change pattern 9 2) else d1025 (change pattern 9 2)) = d2299 pattern
  rw [s2487, s2483]
  rfl
theorem s2489 (pattern : Twelve) : d1027 (change pattern 9 2) = d2299 pattern := by
  change (if pattern.g then d1022 (change pattern 9 2) else d1021 (change pattern 9 2)) = d2299 pattern
  rw [s2487, s2481]
  rfl
theorem s2490 (pattern : Twelve) : d1028 (change pattern 9 2) = d2299 pattern := by
  change (if pattern.b then d1027 (change pattern 9 2) else d1026 (change pattern 9 2)) = d2299 pattern
  rw [s2489, s2488]
  simp only [ite_self]
theorem s2491 (pattern : Twelve) : d1029 (change pattern 9 2) = d2299 pattern := by
  change (if pattern.a then d1027 (change pattern 9 2) else d1028 (change pattern 9 2)) = d2299 pattern
  rw [s2489, s2490]
  simp only [ite_self]
theorem s2492 (pattern : Twelve) : d1275 (change pattern 9 2) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 9 2) else d7 (change pattern 9 2)) = d1275 pattern
  rw [s2434, s2428]
  rfl
theorem s2493 (pattern : Twelve) : d872 (change pattern 9 2) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 9 2) else d1 (change pattern 9 2)) = d872 pattern
  rw [s2434, s2426]
  rfl
theorem s2494 (pattern : Twelve) : d1278 (change pattern 9 2) = d1278 pattern := by
  change (if pattern.i then d872 (change pattern 9 2) else d1275 (change pattern 9 2)) = d1278 pattern
  rw [s2493, s2492]
  rfl
theorem s2495 (pattern : Twelve) : d1284 (change pattern 9 2) = d1284 pattern := by
  change (if pattern.h then d872 (change pattern 9 2) else d1278 (change pattern 9 2)) = d1284 pattern
  rw [s2493, s2494]
  rfl
theorem s2496 (pattern : Twelve) : d1293 (change pattern 9 2) = d1293 pattern := by
  change (if pattern.f then d1284 (change pattern 9 2) else d17 (change pattern 9 2)) = d1293 pattern
  rw [s2495, s2429]
  rfl
theorem s2497 (pattern : Twelve) : d1294 (change pattern 9 2) = d1294 pattern := by
  change (if pattern.f then d6 (change pattern 9 2) else d19 (change pattern 9 2)) = d1294 pattern
  rw [s2442, s2441]
  rfl
theorem s2498 (pattern : Twelve) : d1305 (change pattern 9 2) = d1305 pattern := by
  change (if pattern.e then d1294 (change pattern 9 2) else d1293 (change pattern 9 2)) = d1305 pattern
  rw [s2497, s2496]
  rfl
theorem s2499 (pattern : Twelve) : d1436 (change pattern 9 2) = d1305 pattern := by
  change d1305 (change pattern 9 2) = d1305 pattern
  exact s2498 pattern
theorem s2500 (pattern : Twelve) : d1439 (change pattern 9 2) = d1305 pattern := by
  change d1436 (change pattern 9 2) = d1305 pattern
  exact s2499 pattern
theorem s2501 (pattern : Twelve) : d1283 (change pattern 9 2) = d1283 pattern := by
  change (if pattern.i then d23 (change pattern 9 2) else d19 (change pattern 9 2)) = d1283 pattern
  rw [s2448, s2441]
  rfl
theorem s2502 (pattern : Twelve) : d1301 (change pattern 9 2) = d1301 pattern := by
  change (if pattern.f then d6 (change pattern 9 2) else d1283 (change pattern 9 2)) = d1301 pattern
  rw [s2442, s2501]
  rfl
theorem s2503 (pattern : Twelve) : d1309 (change pattern 9 2) = d1309 pattern := by
  change (if pattern.e then d1301 (change pattern 9 2) else d1293 (change pattern 9 2)) = d1309 pattern
  rw [s2502, s2496]
  rfl
theorem s2504 (pattern : Twelve) : d1437 (change pattern 9 2) = d1309 pattern := by
  change d1309 (change pattern 9 2) = d1309 pattern
  exact s2503 pattern
theorem s2505 (pattern : Twelve) : d1440 (change pattern 9 2) = d2300 pattern := by
  change (if pattern.g then d1437 (change pattern 9 2) else d1439 (change pattern 9 2)) = d2300 pattern
  rw [s2504, s2500]
  rfl
theorem s2506 (pattern : Twelve) : d1441 (change pattern 9 2) = d2300 pattern := by
  change (if pattern.g then d1437 (change pattern 9 2) else d1436 (change pattern 9 2)) = d2300 pattern
  rw [s2504, s2499]
  rfl
theorem s2507 (pattern : Twelve) : d1442 (change pattern 9 2) = d2300 pattern := by
  change (if pattern.b then d1441 (change pattern 9 2) else d1440 (change pattern 9 2)) = d2300 pattern
  rw [s2506, s2505]
  simp only [ite_self]
theorem s2508 (pattern : Twelve) : d1443 (change pattern 9 2) = d2300 pattern := by
  change (if pattern.a then d1441 (change pattern 9 2) else d1442 (change pattern 9 2)) = d2300 pattern
  rw [s2506, s2507]
  simp only [ite_self]
theorem s2509 (pattern : Twelve) : d1324 (change pattern 9 2) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 9 2) else d11 (change pattern 9 2)) = d1324 pattern
  rw [s2471, s2440]
  rfl
theorem s2510 (pattern : Twelve) : d1649 (change pattern 9 2) = d1649 pattern := by
  change (if pattern.f then d1324 (change pattern 9 2) else d19 (change pattern 9 2)) = d1649 pattern
  rw [s2509, s2441]
  rfl
theorem s2511 (pattern : Twelve) : d1650 (change pattern 9 2) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 9 2) else d25 (change pattern 9 2)) = d1650 pattern
  rw [s2442, s2474]
  rfl
theorem s2512 (pattern : Twelve) : d1656 (change pattern 9 2) = d1656 pattern := by
  change (if pattern.e then d1650 (change pattern 9 2) else d1649 (change pattern 9 2)) = d1656 pattern
  rw [s2511, s2510]
  rfl
theorem s2513 (pattern : Twelve) : d1715 (change pattern 9 2) = d1656 pattern := by
  change d1656 (change pattern 9 2) = d1656 pattern
  exact s2512 pattern
theorem s2514 (pattern : Twelve) : d0 (change pattern 8 7) = d0 pattern := by
  rfl
theorem s2515 (pattern : Twelve) : d171 (change pattern 8 7) = d0 pattern := by
  change d0 (change pattern 8 7) = d0 pattern
  exact s2514 pattern
theorem s2516 (pattern : Twelve) : d184 (change pattern 8 7) = d0 pattern := by
  change d171 (change pattern 8 7) = d0 pattern
  exact s2515 pattern
theorem s2517 (pattern : Twelve) : d1 (change pattern 8 7) = d1 pattern := by
  rfl
theorem s2518 (pattern : Twelve) : d7 (change pattern 8 7) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 8 7) else d0 (change pattern 8 7)) = d7 pattern
  rw [s2517, s2514]
  rfl
theorem s2519 (pattern : Twelve) : d17 (change pattern 8 7) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 8 7) else d0 (change pattern 8 7)) = d17 pattern
  rw [s2518, s2514]
  rfl
theorem s2520 (pattern : Twelve) : d366 (change pattern 8 7) = d17 pattern := by
  change d17 (change pattern 8 7) = d17 pattern
  exact s2519 pattern
theorem s2521 (pattern : Twelve) : d372 (change pattern 8 7) = d17 pattern := by
  change d366 (change pattern 8 7) = d17 pattern
  exact s2520 pattern
theorem s2522 (pattern : Twelve) : d389 (change pattern 8 7) = d2302 pattern := by
  change (if pattern.f then d372 (change pattern 8 7) else d184 (change pattern 8 7)) = d2302 pattern
  rw [s2521, s2516]
  rfl
theorem s2523 (pattern : Twelve) : d367 (change pattern 8 7) = d0 pattern := by
  change d0 (change pattern 8 7) = d0 pattern
  exact s2514 pattern
theorem s2524 (pattern : Twelve) : d373 (change pattern 8 7) = d0 pattern := by
  change d367 (change pattern 8 7) = d0 pattern
  exact s2523 pattern
theorem s2525 (pattern : Twelve) : d2 (change pattern 8 7) = d2 pattern := by
  rfl
theorem s2526 (pattern : Twelve) : d10 (change pattern 8 7) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 8 7) else d0 (change pattern 8 7)) = d10 pattern
  rw [s2525, s2514]
  rfl
theorem s2527 (pattern : Twelve) : d3 (change pattern 8 7) = d3 pattern := by
  rfl
theorem s2528 (pattern : Twelve) : d11 (change pattern 8 7) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 8 7) else d1 (change pattern 8 7)) = d11 pattern
  rw [s2527, s2517]
  rfl
theorem s2529 (pattern : Twelve) : d19 (change pattern 8 7) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 8 7) else d10 (change pattern 8 7)) = d19 pattern
  rw [s2528, s2526]
  rfl
theorem s2530 (pattern : Twelve) : d29 (change pattern 8 7) = d19 pattern := by
  change d19 (change pattern 8 7) = d19 pattern
  exact s2529 pattern
theorem s2531 (pattern : Twelve) : d374 (change pattern 8 7) = d19 pattern := by
  change d29 (change pattern 8 7) = d19 pattern
  exact s2530 pattern
theorem s2532 (pattern : Twelve) : d390 (change pattern 8 7) = d2303 pattern := by
  change (if pattern.f then d374 (change pattern 8 7) else d373 (change pattern 8 7)) = d2303 pattern
  rw [s2531, s2524]
  rfl
theorem s2533 (pattern : Twelve) : d402 (change pattern 8 7) = d2304 pattern := by
  change (if pattern.e then d390 (change pattern 8 7) else d389 (change pattern 8 7)) = d2304 pattern
  rw [s2532, s2522]
  rfl
theorem s2534 (pattern : Twelve) : d369 (change pattern 8 7) = d0 pattern := by
  change d0 (change pattern 8 7) = d0 pattern
  exact s2514 pattern
theorem s2535 (pattern : Twelve) : d375 (change pattern 8 7) = d0 pattern := by
  change d369 (change pattern 8 7) = d0 pattern
  exact s2534 pattern
theorem s2536 (pattern : Twelve) : d36 (change pattern 8 7) = d17 pattern := by
  change d17 (change pattern 8 7) = d17 pattern
  exact s2519 pattern
theorem s2537 (pattern : Twelve) : d376 (change pattern 8 7) = d17 pattern := by
  change d36 (change pattern 8 7) = d17 pattern
  exact s2536 pattern
theorem s2538 (pattern : Twelve) : d391 (change pattern 8 7) = d2302 pattern := by
  change (if pattern.f then d376 (change pattern 8 7) else d375 (change pattern 8 7)) = d2302 pattern
  rw [s2537, s2535]
  rfl
theorem s2539 (pattern : Twelve) : d35 (change pattern 8 7) = d0 pattern := by
  change d0 (change pattern 8 7) = d0 pattern
  exact s2514 pattern
theorem s2540 (pattern : Twelve) : d377 (change pattern 8 7) = d0 pattern := by
  change d35 (change pattern 8 7) = d0 pattern
  exact s2539 pattern
theorem s2541 (pattern : Twelve) : d378 (change pattern 8 7) = d19 pattern := by
  change d29 (change pattern 8 7) = d19 pattern
  exact s2530 pattern
theorem s2542 (pattern : Twelve) : d392 (change pattern 8 7) = d2303 pattern := by
  change (if pattern.f then d378 (change pattern 8 7) else d377 (change pattern 8 7)) = d2303 pattern
  rw [s2541, s2540]
  rfl
theorem s2543 (pattern : Twelve) : d403 (change pattern 8 7) = d2304 pattern := by
  change (if pattern.e then d392 (change pattern 8 7) else d391 (change pattern 8 7)) = d2304 pattern
  rw [s2542, s2538]
  rfl
theorem s2544 (pattern : Twelve) : d409 (change pattern 8 7) = d2304 pattern := by
  change (if pattern.j then d403 (change pattern 8 7) else d402 (change pattern 8 7)) = d2304 pattern
  rw [s2543, s2533]
  simp only [ite_self]
theorem s2545 (pattern : Twelve) : d379 (change pattern 8 7) = d0 pattern := by
  change d35 (change pattern 8 7) = d0 pattern
  exact s2539 pattern
theorem s2546 (pattern : Twelve) : d380 (change pattern 8 7) = d17 pattern := by
  change d36 (change pattern 8 7) = d17 pattern
  exact s2536 pattern
theorem s2547 (pattern : Twelve) : d393 (change pattern 8 7) = d2302 pattern := by
  change (if pattern.f then d380 (change pattern 8 7) else d379 (change pattern 8 7)) = d2302 pattern
  rw [s2546, s2545]
  rfl
theorem s2548 (pattern : Twelve) : d394 (change pattern 8 7) = d2303 pattern := by
  change (if pattern.f then d378 (change pattern 8 7) else d35 (change pattern 8 7)) = d2303 pattern
  rw [s2541, s2539]
  rfl
theorem s2549 (pattern : Twelve) : d404 (change pattern 8 7) = d2304 pattern := by
  change (if pattern.e then d394 (change pattern 8 7) else d393 (change pattern 8 7)) = d2304 pattern
  rw [s2548, s2547]
  rfl
end NetHack.Sokoban21.Diagram
