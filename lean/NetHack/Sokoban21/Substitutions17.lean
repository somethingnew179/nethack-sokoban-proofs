/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions16
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s2550 (pattern : Twelve) : d410 (change pattern 8 7) = d2304 pattern := by
  change (if pattern.j then d404 (change pattern 8 7) else d403 (change pattern 8 7)) = d2304 pattern
  rw [s2549, s2543]
  simp only [ite_self]
theorem s2551 (pattern : Twelve) : d415 (change pattern 8 7) = d2304 pattern := by
  change (if pattern.d then d410 (change pattern 8 7) else d409 (change pattern 8 7)) = d2304 pattern
  rw [s2550, s2544]
  simp only [ite_self]
theorem s2552 (pattern : Twelve) : d371 (change pattern 8 7) = d0 pattern := by
  change d0 (change pattern 8 7) = d0 pattern
  exact s2514 pattern
theorem s2553 (pattern : Twelve) : d381 (change pattern 8 7) = d0 pattern := by
  change d371 (change pattern 8 7) = d0 pattern
  exact s2552 pattern
theorem s2554 (pattern : Twelve) : d382 (change pattern 8 7) = d17 pattern := by
  change d36 (change pattern 8 7) = d17 pattern
  exact s2536 pattern
theorem s2555 (pattern : Twelve) : d395 (change pattern 8 7) = d2302 pattern := by
  change (if pattern.f then d382 (change pattern 8 7) else d381 (change pattern 8 7)) = d2302 pattern
  rw [s2554, s2553]
  rfl
theorem s2556 (pattern : Twelve) : d383 (change pattern 8 7) = d0 pattern := by
  change d35 (change pattern 8 7) = d0 pattern
  exact s2539 pattern
theorem s2557 (pattern : Twelve) : d396 (change pattern 8 7) = d2303 pattern := by
  change (if pattern.f then d378 (change pattern 8 7) else d383 (change pattern 8 7)) = d2303 pattern
  rw [s2541, s2556]
  rfl
theorem s2558 (pattern : Twelve) : d405 (change pattern 8 7) = d2304 pattern := by
  change (if pattern.e then d396 (change pattern 8 7) else d395 (change pattern 8 7)) = d2304 pattern
  rw [s2557, s2555]
  rfl
theorem s2559 (pattern : Twelve) : d39 (change pattern 8 7) = d2 pattern := by
  change d2 (change pattern 8 7) = d2 pattern
  exact s2525 pattern
theorem s2560 (pattern : Twelve) : d9 (change pattern 8 7) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 8 7) else d2 (change pattern 8 7)) = d9 pattern
  rw [s2527, s2525]
  rfl
theorem s2561 (pattern : Twelve) : d23 (change pattern 8 7) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 8 7) else d2 (change pattern 8 7)) = d23 pattern
  rw [s2560, s2525]
  rfl
theorem s2562 (pattern : Twelve) : d40 (change pattern 8 7) = d23 pattern := by
  change d23 (change pattern 8 7) = d23 pattern
  exact s2561 pattern
theorem s2563 (pattern : Twelve) : d384 (change pattern 8 7) = d23 pattern := by
  change d40 (change pattern 8 7) = d23 pattern
  exact s2562 pattern
theorem s2564 (pattern : Twelve) : d397 (change pattern 8 7) = d1943 pattern := by
  change (if pattern.f then d384 (change pattern 8 7) else d39 (change pattern 8 7)) = d1943 pattern
  rw [s2563, s2559]
  rfl
theorem s2565 (pattern : Twelve) : d4 (change pattern 8 7) = d4 pattern := by
  rfl
theorem s2566 (pattern : Twelve) : d16 (change pattern 8 7) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 8 7) else d2 (change pattern 8 7)) = d16 pattern
  rw [s2565, s2525]
  rfl
theorem s2567 (pattern : Twelve) : d5 (change pattern 8 7) = d5 pattern := by
  rfl
theorem s2568 (pattern : Twelve) : d12 (change pattern 8 7) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 8 7) else d3 (change pattern 8 7)) = d12 pattern
  rw [s2567, s2527]
  rfl
theorem s2569 (pattern : Twelve) : d25 (change pattern 8 7) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 8 7) else d16 (change pattern 8 7)) = d25 pattern
  rw [s2568, s2566]
  rfl
theorem s2570 (pattern : Twelve) : d42 (change pattern 8 7) = d25 pattern := by
  change d25 (change pattern 8 7) = d25 pattern
  exact s2569 pattern
theorem s2571 (pattern : Twelve) : d385 (change pattern 8 7) = d25 pattern := by
  change d42 (change pattern 8 7) = d25 pattern
  exact s2570 pattern
theorem s2572 (pattern : Twelve) : d398 (change pattern 8 7) = d1971 pattern := by
  change (if pattern.f then d385 (change pattern 8 7) else d39 (change pattern 8 7)) = d1971 pattern
  rw [s2571, s2559]
  rfl
theorem s2573 (pattern : Twelve) : d406 (change pattern 8 7) = d2305 pattern := by
  change (if pattern.e then d398 (change pattern 8 7) else d397 (change pattern 8 7)) = d2305 pattern
  rw [s2572, s2564]
  rfl
theorem s2574 (pattern : Twelve) : d411 (change pattern 8 7) = d2306 pattern := by
  change (if pattern.j then d406 (change pattern 8 7) else d405 (change pattern 8 7)) = d2306 pattern
  rw [s2573, s2558]
  rfl
theorem s2575 (pattern : Twelve) : d399 (change pattern 8 7) = d2302 pattern := by
  change (if pattern.f then d380 (change pattern 8 7) else d35 (change pattern 8 7)) = d2302 pattern
  rw [s2546, s2539]
  rfl
theorem s2576 (pattern : Twelve) : d407 (change pattern 8 7) = d2304 pattern := by
  change (if pattern.e then d394 (change pattern 8 7) else d399 (change pattern 8 7)) = d2304 pattern
  rw [s2548, s2575]
  rfl
theorem s2577 (pattern : Twelve) : d6 (change pattern 8 7) = d6 pattern := by
  rfl
theorem s2578 (pattern : Twelve) : d412 (change pattern 8 7) = d2307 pattern := by
  change (if pattern.j then d6 (change pattern 8 7) else d407 (change pattern 8 7)) = d2307 pattern
  rw [s2577, s2576]
  rfl
theorem s2579 (pattern : Twelve) : d416 (change pattern 8 7) = d2308 pattern := by
  change (if pattern.d then d412 (change pattern 8 7) else d411 (change pattern 8 7)) = d2308 pattern
  rw [s2578, s2574]
  rfl
theorem s2580 (pattern : Twelve) : d419 (change pattern 8 7) = d2309 pattern := by
  change (if pattern.c then d416 (change pattern 8 7) else d415 (change pattern 8 7)) = d2309 pattern
  rw [s2579, s2551]
  rfl
theorem s2581 (pattern : Twelve) : d413 (change pattern 8 7) = d2306 pattern := by
  change (if pattern.j then d406 (change pattern 8 7) else d407 (change pattern 8 7)) = d2306 pattern
  rw [s2573, s2576]
  rfl
theorem s2582 (pattern : Twelve) : d417 (change pattern 8 7) = d2308 pattern := by
  change (if pattern.d then d412 (change pattern 8 7) else d413 (change pattern 8 7)) = d2308 pattern
  rw [s2578, s2581]
  rfl
theorem s2583 (pattern : Twelve) : d420 (change pattern 8 7) = d2309 pattern := by
  change (if pattern.c then d417 (change pattern 8 7) else d407 (change pattern 8 7)) = d2309 pattern
  rw [s2582, s2576]
  rfl
theorem s2584 (pattern : Twelve) : d422 (change pattern 8 7) = d2309 pattern := by
  change (if pattern.g then d420 (change pattern 8 7) else d419 (change pattern 8 7)) = d2309 pattern
  rw [s2583, s2580]
  simp only [ite_self]
theorem s2585 (pattern : Twelve) : d423 (change pattern 8 7) = d2309 pattern := by
  change (if pattern.b then d420 (change pattern 8 7) else d422 (change pattern 8 7)) = d2309 pattern
  rw [s2583, s2584]
  simp only [ite_self]
theorem s2586 (pattern : Twelve) : d117 (change pattern 8 7) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 8 7) else d3 (change pattern 8 7)) = d117 pattern
  rw [s2565, s2527]
  rfl
theorem s2587 (pattern : Twelve) : d119 (change pattern 8 7) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 8 7) else d3 (change pattern 8 7)) = d119 pattern
  rw [s2586, s2527]
  rfl
theorem s2588 (pattern : Twelve) : d125 (change pattern 8 7) = d119 pattern := by
  change d119 (change pattern 8 7) = d119 pattern
  exact s2587 pattern
theorem s2589 (pattern : Twelve) : d386 (change pattern 8 7) = d119 pattern := by
  change d125 (change pattern 8 7) = d119 pattern
  exact s2588 pattern
theorem s2590 (pattern : Twelve) : d400 (change pattern 8 7) = d2310 pattern := by
  change (if pattern.f then d386 (change pattern 8 7) else d39 (change pattern 8 7)) = d2310 pattern
  rw [s2589, s2559]
  rfl
theorem s2591 (pattern : Twelve) : d47 (change pattern 8 7) = d3 pattern := by
  change d3 (change pattern 8 7) = d3 pattern
  exact s2527 pattern
theorem s2592 (pattern : Twelve) : d387 (change pattern 8 7) = d3 pattern := by
  change d47 (change pattern 8 7) = d3 pattern
  exact s2591 pattern
theorem s2593 (pattern : Twelve) : d13 (change pattern 8 7) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 8 7) else d4 (change pattern 8 7)) = d13 pattern
  rw [s2577, s2565]
  rfl
theorem s2594 (pattern : Twelve) : d20 (change pattern 8 7) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 8 7) else d12 (change pattern 8 7)) = d20 pattern
  rw [s2593, s2568]
  rfl
theorem s2595 (pattern : Twelve) : d128 (change pattern 8 7) = d20 pattern := by
  change d20 (change pattern 8 7) = d20 pattern
  exact s2594 pattern
theorem s2596 (pattern : Twelve) : d388 (change pattern 8 7) = d20 pattern := by
  change d128 (change pattern 8 7) = d20 pattern
  exact s2595 pattern
theorem s2597 (pattern : Twelve) : d401 (change pattern 8 7) = d2311 pattern := by
  change (if pattern.f then d388 (change pattern 8 7) else d387 (change pattern 8 7)) = d2311 pattern
  rw [s2596, s2592]
  rfl
theorem s2598 (pattern : Twelve) : d408 (change pattern 8 7) = d2312 pattern := by
  change (if pattern.e then d401 (change pattern 8 7) else d400 (change pattern 8 7)) = d2312 pattern
  rw [s2597, s2590]
  rfl
theorem s2599 (pattern : Twelve) : d414 (change pattern 8 7) = d2313 pattern := by
  change (if pattern.j then d408 (change pattern 8 7) else d407 (change pattern 8 7)) = d2313 pattern
  rw [s2598, s2576]
  rfl
theorem s2600 (pattern : Twelve) : d418 (change pattern 8 7) = d2314 pattern := by
  change (if pattern.d then d412 (change pattern 8 7) else d414 (change pattern 8 7)) = d2314 pattern
  rw [s2578, s2599]
  rfl
theorem s2601 (pattern : Twelve) : d421 (change pattern 8 7) = d2315 pattern := by
  change (if pattern.c then d418 (change pattern 8 7) else d407 (change pattern 8 7)) = d2315 pattern
  rw [s2600, s2576]
  rfl
theorem s2602 (pattern : Twelve) : d424 (change pattern 8 7) = d2316 pattern := by
  change (if pattern.a then d421 (change pattern 8 7) else d423 (change pattern 8 7)) = d2316 pattern
  rw [s2601, s2585]
  rfl
theorem s2603 (pattern : Twelve) : d814 (change pattern 8 7) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 8 7) else d7 (change pattern 8 7)) = d814 pattern
  rw [s2517, s2518]
  rfl
theorem s2604 (pattern : Twelve) : d818 (change pattern 8 7) = d814 pattern := by
  change d814 (change pattern 8 7) = d814 pattern
  exact s2603 pattern
theorem s2605 (pattern : Twelve) : d1030 (change pattern 8 7) = d814 pattern := by
  change d818 (change pattern 8 7) = d814 pattern
  exact s2604 pattern
theorem s2606 (pattern : Twelve) : d1038 (change pattern 8 7) = d2317 pattern := by
  change (if pattern.f then d1030 (change pattern 8 7) else d373 (change pattern 8 7)) = d2317 pattern
  rw [s2605, s2524]
  rfl
theorem s2607 (pattern : Twelve) : d1031 (change pattern 8 7) = d17 pattern := by
  change d36 (change pattern 8 7) = d17 pattern
  exact s2536 pattern
theorem s2608 (pattern : Twelve) : d1032 (change pattern 8 7) = d25 pattern := by
  change d42 (change pattern 8 7) = d25 pattern
  exact s2570 pattern
theorem s2609 (pattern : Twelve) : d1039 (change pattern 8 7) = d1960 pattern := by
  change (if pattern.f then d1032 (change pattern 8 7) else d1031 (change pattern 8 7)) = d1960 pattern
  rw [s2608, s2607]
  rfl
theorem s2610 (pattern : Twelve) : d1048 (change pattern 8 7) = d2318 pattern := by
  change (if pattern.e then d1039 (change pattern 8 7) else d1038 (change pattern 8 7)) = d2318 pattern
  rw [s2609, s2606]
  rfl
theorem s2611 (pattern : Twelve) : d1033 (change pattern 8 7) = d814 pattern := by
  change d818 (change pattern 8 7) = d814 pattern
  exact s2604 pattern
theorem s2612 (pattern : Twelve) : d1040 (change pattern 8 7) = d2317 pattern := by
  change (if pattern.f then d1033 (change pattern 8 7) else d377 (change pattern 8 7)) = d2317 pattern
  rw [s2611, s2540]
  rfl
theorem s2613 (pattern : Twelve) : d1041 (change pattern 8 7) = d1960 pattern := by
  change (if pattern.f then d1032 (change pattern 8 7) else d36 (change pattern 8 7)) = d1960 pattern
  rw [s2608, s2536]
  rfl
theorem s2614 (pattern : Twelve) : d1049 (change pattern 8 7) = d2318 pattern := by
  change (if pattern.e then d1041 (change pattern 8 7) else d1040 (change pattern 8 7)) = d2318 pattern
  rw [s2613, s2612]
  rfl
theorem s2615 (pattern : Twelve) : d1054 (change pattern 8 7) = d2318 pattern := by
  change (if pattern.j then d1049 (change pattern 8 7) else d1048 (change pattern 8 7)) = d2318 pattern
  rw [s2614, s2610]
  simp only [ite_self]
theorem s2616 (pattern : Twelve) : d1042 (change pattern 8 7) = d2317 pattern := by
  change (if pattern.f then d1033 (change pattern 8 7) else d35 (change pattern 8 7)) = d2317 pattern
  rw [s2611, s2539]
  rfl
theorem s2617 (pattern : Twelve) : d1050 (change pattern 8 7) = d2318 pattern := by
  change (if pattern.e then d1041 (change pattern 8 7) else d1042 (change pattern 8 7)) = d2318 pattern
  rw [s2613, s2616]
  rfl
theorem s2618 (pattern : Twelve) : d1055 (change pattern 8 7) = d2318 pattern := by
  change (if pattern.j then d1050 (change pattern 8 7) else d1049 (change pattern 8 7)) = d2318 pattern
  rw [s2617, s2614]
  simp only [ite_self]
theorem s2619 (pattern : Twelve) : d1060 (change pattern 8 7) = d2318 pattern := by
  change (if pattern.d then d1055 (change pattern 8 7) else d1054 (change pattern 8 7)) = d2318 pattern
  rw [s2618, s2615]
  simp only [ite_self]
theorem s2620 (pattern : Twelve) : d1043 (change pattern 8 7) = d2317 pattern := by
  change (if pattern.f then d1033 (change pattern 8 7) else d383 (change pattern 8 7)) = d2317 pattern
  rw [s2611, s2556]
  rfl
theorem s2621 (pattern : Twelve) : d1051 (change pattern 8 7) = d2318 pattern := by
  change (if pattern.e then d1041 (change pattern 8 7) else d1043 (change pattern 8 7)) = d2318 pattern
  rw [s2613, s2620]
  rfl
theorem s2622 (pattern : Twelve) : d815 (change pattern 8 7) = d815 pattern := by
  change (if pattern.k then d3 (change pattern 8 7) else d9 (change pattern 8 7)) = d815 pattern
  rw [s2527, s2560]
  rfl
theorem s2623 (pattern : Twelve) : d820 (change pattern 8 7) = d815 pattern := by
  change d815 (change pattern 8 7) = d815 pattern
  exact s2622 pattern
theorem s2624 (pattern : Twelve) : d1034 (change pattern 8 7) = d815 pattern := by
  change d820 (change pattern 8 7) = d815 pattern
  exact s2623 pattern
theorem s2625 (pattern : Twelve) : d1044 (change pattern 8 7) = d2319 pattern := by
  change (if pattern.f then d1034 (change pattern 8 7) else d39 (change pattern 8 7)) = d2319 pattern
  rw [s2624, s2559]
  rfl
theorem s2626 (pattern : Twelve) : d14 (change pattern 8 7) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 8 7) else d5 (change pattern 8 7)) = d14 pattern
  rw [s2577, s2567]
  rfl
theorem s2627 (pattern : Twelve) : d21 (change pattern 8 7) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 8 7) else d13 (change pattern 8 7)) = d21 pattern
  rw [s2626, s2593]
  rfl
theorem s2628 (pattern : Twelve) : d822 (change pattern 8 7) = d21 pattern := by
  change d21 (change pattern 8 7) = d21 pattern
  exact s2627 pattern
theorem s2629 (pattern : Twelve) : d1035 (change pattern 8 7) = d21 pattern := by
  change d822 (change pattern 8 7) = d21 pattern
  exact s2628 pattern
theorem s2630 (pattern : Twelve) : d1045 (change pattern 8 7) = d2320 pattern := by
  change (if pattern.f then d1035 (change pattern 8 7) else d40 (change pattern 8 7)) = d2320 pattern
  rw [s2629, s2562]
  rfl
theorem s2631 (pattern : Twelve) : d1052 (change pattern 8 7) = d2321 pattern := by
  change (if pattern.e then d1045 (change pattern 8 7) else d1044 (change pattern 8 7)) = d2321 pattern
  rw [s2630, s2625]
  rfl
theorem s2632 (pattern : Twelve) : d1056 (change pattern 8 7) = d2322 pattern := by
  change (if pattern.j then d1052 (change pattern 8 7) else d1051 (change pattern 8 7)) = d2322 pattern
  rw [s2631, s2621]
  rfl
theorem s2633 (pattern : Twelve) : d1057 (change pattern 8 7) = d2323 pattern := by
  change (if pattern.j then d6 (change pattern 8 7) else d1050 (change pattern 8 7)) = d2323 pattern
  rw [s2577, s2617]
  rfl
theorem s2634 (pattern : Twelve) : d1061 (change pattern 8 7) = d2324 pattern := by
  change (if pattern.d then d1057 (change pattern 8 7) else d1056 (change pattern 8 7)) = d2324 pattern
  rw [s2633, s2632]
  rfl
theorem s2635 (pattern : Twelve) : d1064 (change pattern 8 7) = d2325 pattern := by
  change (if pattern.c then d1061 (change pattern 8 7) else d1060 (change pattern 8 7)) = d2325 pattern
  rw [s2634, s2619]
  rfl
theorem s2636 (pattern : Twelve) : d1058 (change pattern 8 7) = d2322 pattern := by
  change (if pattern.j then d1052 (change pattern 8 7) else d1050 (change pattern 8 7)) = d2322 pattern
  rw [s2631, s2617]
  rfl
theorem s2637 (pattern : Twelve) : d1062 (change pattern 8 7) = d2324 pattern := by
  change (if pattern.d then d1057 (change pattern 8 7) else d1058 (change pattern 8 7)) = d2324 pattern
  rw [s2633, s2636]
  rfl
theorem s2638 (pattern : Twelve) : d1065 (change pattern 8 7) = d2325 pattern := by
  change (if pattern.c then d1062 (change pattern 8 7) else d1050 (change pattern 8 7)) = d2325 pattern
  rw [s2637, s2617]
  rfl
theorem s2639 (pattern : Twelve) : d1067 (change pattern 8 7) = d2325 pattern := by
  change (if pattern.g then d1065 (change pattern 8 7) else d1064 (change pattern 8 7)) = d2325 pattern
  rw [s2638, s2635]
  simp only [ite_self]
theorem s2640 (pattern : Twelve) : d1068 (change pattern 8 7) = d2325 pattern := by
  change (if pattern.b then d1065 (change pattern 8 7) else d1067 (change pattern 8 7)) = d2325 pattern
  rw [s2638, s2639]
  simp only [ite_self]
theorem s2641 (pattern : Twelve) : d15 (change pattern 8 7) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 8 7) else d4 (change pattern 8 7)) = d15 pattern
  rw [s2567, s2565]
  rfl
theorem s2642 (pattern : Twelve) : d873 (change pattern 8 7) = d873 pattern := by
  change (if pattern.k then d15 (change pattern 8 7) else d117 (change pattern 8 7)) = d873 pattern
  rw [s2641, s2586]
  rfl
theorem s2643 (pattern : Twelve) : d880 (change pattern 8 7) = d873 pattern := by
  change d873 (change pattern 8 7) = d873 pattern
  exact s2642 pattern
theorem s2644 (pattern : Twelve) : d1036 (change pattern 8 7) = d873 pattern := by
  change d880 (change pattern 8 7) = d873 pattern
  exact s2643 pattern
theorem s2645 (pattern : Twelve) : d1046 (change pattern 8 7) = d2326 pattern := by
  change (if pattern.f then d1036 (change pattern 8 7) else d39 (change pattern 8 7)) = d2326 pattern
  rw [s2644, s2559]
  rfl
theorem s2646 (pattern : Twelve) : d1037 (change pattern 8 7) = d119 pattern := by
  change d125 (change pattern 8 7) = d119 pattern
  exact s2588 pattern
theorem s2647 (pattern : Twelve) : d889 (change pattern 8 7) = d6 pattern := by
  change d6 (change pattern 8 7) = d6 pattern
  exact s2577 pattern
theorem s2648 (pattern : Twelve) : d1047 (change pattern 8 7) = d2327 pattern := by
  change (if pattern.f then d889 (change pattern 8 7) else d1037 (change pattern 8 7)) = d2327 pattern
  rw [s2647, s2646]
  rfl
theorem s2649 (pattern : Twelve) : d1053 (change pattern 8 7) = d2328 pattern := by
  change (if pattern.e then d1047 (change pattern 8 7) else d1046 (change pattern 8 7)) = d2328 pattern
  rw [s2648, s2645]
  rfl
theorem s2650 (pattern : Twelve) : d1059 (change pattern 8 7) = d2329 pattern := by
  change (if pattern.j then d1053 (change pattern 8 7) else d1050 (change pattern 8 7)) = d2329 pattern
  rw [s2649, s2617]
  rfl
theorem s2651 (pattern : Twelve) : d1063 (change pattern 8 7) = d2330 pattern := by
  change (if pattern.d then d1057 (change pattern 8 7) else d1059 (change pattern 8 7)) = d2330 pattern
  rw [s2633, s2650]
  rfl
theorem s2652 (pattern : Twelve) : d1066 (change pattern 8 7) = d2331 pattern := by
  change (if pattern.c then d1063 (change pattern 8 7) else d1050 (change pattern 8 7)) = d2331 pattern
  rw [s2651, s2617]
  rfl
theorem s2653 (pattern : Twelve) : d1069 (change pattern 8 7) = d2332 pattern := by
  change (if pattern.a then d1066 (change pattern 8 7) else d1068 (change pattern 8 7)) = d2332 pattern
  rw [s2652, s2640]
  rfl
theorem s2654 (pattern : Twelve) : d8 (change pattern 8 7) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 8 7) else d1 (change pattern 8 7)) = d8 pattern
  rw [s2525, s2517]
  rfl
theorem s2655 (pattern : Twelve) : d872 (change pattern 8 7) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 8 7) else d1 (change pattern 8 7)) = d872 pattern
  rw [s2654, s2517]
  rfl
theorem s2656 (pattern : Twelve) : d1280 (change pattern 8 7) = d872 pattern := by
  change d872 (change pattern 8 7) = d872 pattern
  exact s2655 pattern
theorem s2657 (pattern : Twelve) : d1445 (change pattern 8 7) = d872 pattern := by
  change d1280 (change pattern 8 7) = d872 pattern
  exact s2656 pattern
theorem s2658 (pattern : Twelve) : d1448 (change pattern 8 7) = d1976 pattern := by
  change (if pattern.f then d1445 (change pattern 8 7) else d1031 (change pattern 8 7)) = d1976 pattern
  rw [s2657, s2607]
  rfl
theorem s2659 (pattern : Twelve) : d1449 (change pattern 8 7) = d1294 pattern := by
  change (if pattern.f then d6 (change pattern 8 7) else d29 (change pattern 8 7)) = d1294 pattern
  rw [s2577, s2530]
  rfl
theorem s2660 (pattern : Twelve) : d1455 (change pattern 8 7) = d1977 pattern := by
  change (if pattern.e then d1449 (change pattern 8 7) else d1448 (change pattern 8 7)) = d1977 pattern
  rw [s2659, s2658]
  rfl
theorem s2661 (pattern : Twelve) : d1450 (change pattern 8 7) = d1976 pattern := by
  change (if pattern.f then d1445 (change pattern 8 7) else d36 (change pattern 8 7)) = d1976 pattern
  rw [s2657, s2536]
  rfl
theorem s2662 (pattern : Twelve) : d1456 (change pattern 8 7) = d1977 pattern := by
  change (if pattern.e then d1449 (change pattern 8 7) else d1450 (change pattern 8 7)) = d1977 pattern
  rw [s2659, s2661]
  rfl
theorem s2663 (pattern : Twelve) : d1459 (change pattern 8 7) = d1977 pattern := by
  change (if pattern.j then d1456 (change pattern 8 7) else d1455 (change pattern 8 7)) = d1977 pattern
  rw [s2662, s2660]
  simp only [ite_self]
theorem s2664 (pattern : Twelve) : d1463 (change pattern 8 7) = d1977 pattern := by
  change (if pattern.d then d1456 (change pattern 8 7) else d1459 (change pattern 8 7)) = d1977 pattern
  rw [s2662, s2663]
  simp only [ite_self]
theorem s2665 (pattern : Twelve) : d1446 (change pattern 8 7) = d119 pattern := by
  change d125 (change pattern 8 7) = d119 pattern
  exact s2588 pattern
theorem s2666 (pattern : Twelve) : d1451 (change pattern 8 7) = d2333 pattern := by
  change (if pattern.f then d1446 (change pattern 8 7) else d40 (change pattern 8 7)) = d2333 pattern
  rw [s2665, s2562]
  rfl
theorem s2667 (pattern : Twelve) : d1452 (change pattern 8 7) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 8 7) else d42 (change pattern 8 7)) = d1650 pattern
  rw [s2577, s2570]
  rfl
theorem s2668 (pattern : Twelve) : d1457 (change pattern 8 7) = d2334 pattern := by
  change (if pattern.e then d1452 (change pattern 8 7) else d1451 (change pattern 8 7)) = d2334 pattern
  rw [s2667, s2666]
  rfl
theorem s2669 (pattern : Twelve) : d1460 (change pattern 8 7) = d2335 pattern := by
  change (if pattern.j then d1457 (change pattern 8 7) else d1456 (change pattern 8 7)) = d2335 pattern
  rw [s2668, s2662]
  rfl
theorem s2670 (pattern : Twelve) : d1461 (change pattern 8 7) = d2336 pattern := by
  change (if pattern.j then d6 (change pattern 8 7) else d1456 (change pattern 8 7)) = d2336 pattern
  rw [s2577, s2662]
  rfl
theorem s2671 (pattern : Twelve) : d1464 (change pattern 8 7) = d2337 pattern := by
  change (if pattern.d then d1461 (change pattern 8 7) else d1460 (change pattern 8 7)) = d2337 pattern
  rw [s2670, s2669]
  rfl
theorem s2672 (pattern : Twelve) : d1466 (change pattern 8 7) = d2338 pattern := by
  change (if pattern.c then d1464 (change pattern 8 7) else d1463 (change pattern 8 7)) = d2338 pattern
  rw [s2671, s2664]
  rfl
theorem s2673 (pattern : Twelve) : d1467 (change pattern 8 7) = d2338 pattern := by
  change (if pattern.c then d1464 (change pattern 8 7) else d1456 (change pattern 8 7)) = d2338 pattern
  rw [s2671, s2662]
  rfl
theorem s2674 (pattern : Twelve) : d1469 (change pattern 8 7) = d2338 pattern := by
  change (if pattern.g then d1467 (change pattern 8 7) else d1466 (change pattern 8 7)) = d2338 pattern
  rw [s2673, s2672]
  simp only [ite_self]
theorem s2675 (pattern : Twelve) : d1470 (change pattern 8 7) = d2338 pattern := by
  change (if pattern.b then d1467 (change pattern 8 7) else d1469 (change pattern 8 7)) = d2338 pattern
  rw [s2673, s2674]
  simp only [ite_self]
theorem s2676 (pattern : Twelve) : d1277 (change pattern 8 7) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 8 7) else d15 (change pattern 8 7)) = d1277 pattern
  rw [s2626, s2641]
  rfl
theorem s2677 (pattern : Twelve) : d1331 (change pattern 8 7) = d1277 pattern := by
  change d1277 (change pattern 8 7) = d1277 pattern
  exact s2676 pattern
theorem s2678 (pattern : Twelve) : d1337 (change pattern 8 7) = d1277 pattern := by
  change d1331 (change pattern 8 7) = d1277 pattern
  exact s2677 pattern
theorem s2679 (pattern : Twelve) : d1453 (change pattern 8 7) = d2339 pattern := by
  change (if pattern.f then d1337 (change pattern 8 7) else d40 (change pattern 8 7)) = d2339 pattern
  rw [s2678, s2562]
  rfl
theorem s2680 (pattern : Twelve) : d1447 (change pattern 8 7) = d20 pattern := by
  change d128 (change pattern 8 7) = d20 pattern
  exact s2595 pattern
theorem s2681 (pattern : Twelve) : d1454 (change pattern 8 7) = d2340 pattern := by
  change (if pattern.f then d6 (change pattern 8 7) else d1447 (change pattern 8 7)) = d2340 pattern
  rw [s2577, s2680]
  rfl
theorem s2682 (pattern : Twelve) : d1458 (change pattern 8 7) = d2341 pattern := by
  change (if pattern.e then d1454 (change pattern 8 7) else d1453 (change pattern 8 7)) = d2341 pattern
  rw [s2681, s2679]
  rfl
theorem s2683 (pattern : Twelve) : d1462 (change pattern 8 7) = d2342 pattern := by
  change (if pattern.j then d1458 (change pattern 8 7) else d1456 (change pattern 8 7)) = d2342 pattern
  rw [s2682, s2662]
  rfl
theorem s2684 (pattern : Twelve) : d1465 (change pattern 8 7) = d2343 pattern := by
  change (if pattern.d then d1461 (change pattern 8 7) else d1462 (change pattern 8 7)) = d2343 pattern
  rw [s2670, s2683]
  rfl
theorem s2685 (pattern : Twelve) : d1468 (change pattern 8 7) = d2344 pattern := by
  change (if pattern.c then d1465 (change pattern 8 7) else d1456 (change pattern 8 7)) = d2344 pattern
  rw [s2684, s2662]
  rfl
theorem s2686 (pattern : Twelve) : d1471 (change pattern 8 7) = d2345 pattern := by
  change (if pattern.a then d1468 (change pattern 8 7) else d1470 (change pattern 8 7)) = d2345 pattern
  rw [s2685, s2675]
  rfl
theorem s2687 (pattern : Twelve) : d1324 (change pattern 8 7) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 8 7) else d11 (change pattern 8 7)) = d1324 pattern
  rw [s2566, s2528]
  rfl
theorem s2688 (pattern : Twelve) : d1645 (change pattern 8 7) = d1324 pattern := by
  change d1324 (change pattern 8 7) = d1324 pattern
  exact s2687 pattern
theorem s2689 (pattern : Twelve) : d1716 (change pattern 8 7) = d1649 pattern := by
  change (if pattern.f then d1645 (change pattern 8 7) else d29 (change pattern 8 7)) = d1649 pattern
  rw [s2688, s2530]
  rfl
theorem s2690 (pattern : Twelve) : d1719 (change pattern 8 7) = d1656 pattern := by
  change (if pattern.e then d1452 (change pattern 8 7) else d1716 (change pattern 8 7)) = d1656 pattern
  rw [s2667, s2689]
  rfl
theorem s2691 (pattern : Twelve) : d1717 (change pattern 8 7) = d1814 pattern := by
  change (if pattern.f then d128 (change pattern 8 7) else d42 (change pattern 8 7)) = d1814 pattern
  rw [s2595, s2570]
  rfl
theorem s2692 (pattern : Twelve) : d1655 (change pattern 8 7) = d1815 pattern := by
  change (if pattern.f then d6 (change pattern 8 7) else d822 (change pattern 8 7)) = d1815 pattern
  rw [s2577, s2628]
  rfl
theorem s2693 (pattern : Twelve) : d1720 (change pattern 8 7) = d1818 pattern := by
  change (if pattern.e then d1655 (change pattern 8 7) else d1717 (change pattern 8 7)) = d1818 pattern
  rw [s2692, s2691]
  rfl
theorem s2694 (pattern : Twelve) : d1722 (change pattern 8 7) = d1992 pattern := by
  change (if pattern.j then d1720 (change pattern 8 7) else d1719 (change pattern 8 7)) = d1992 pattern
  rw [s2693, s2690]
  rfl
theorem s2695 (pattern : Twelve) : d1723 (change pattern 8 7) = d1715 pattern := by
  change (if pattern.j then d6 (change pattern 8 7) else d1719 (change pattern 8 7)) = d1715 pattern
  rw [s2577, s2690]
  rfl
theorem s2696 (pattern : Twelve) : d1725 (change pattern 8 7) = d2346 pattern := by
  change (if pattern.d then d1723 (change pattern 8 7) else d1722 (change pattern 8 7)) = d2346 pattern
  rw [s2695, s2694]
  rfl
theorem s2697 (pattern : Twelve) : d1727 (change pattern 8 7) = d2347 pattern := by
  change (if pattern.c then d1725 (change pattern 8 7) else d1719 (change pattern 8 7)) = d2347 pattern
  rw [s2696, s2690]
  rfl
theorem s2698 (pattern : Twelve) : d22 (change pattern 8 7) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 8 7) else d14 (change pattern 8 7)) = d22 pattern
  rw [s2577, s2626]
  rfl
theorem s2699 (pattern : Twelve) : d183 (change pattern 8 7) = d22 pattern := by
  change d22 (change pattern 8 7) = d22 pattern
  exact s2698 pattern
end NetHack.Sokoban21.Diagram
