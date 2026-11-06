/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions20
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2520 (p : Pattern) : d401 (change p 138 none) = d46 p := by
  change (if p 134 then d400 (change p 138 none) else d399 (change p 138 none)) = d46 p
  rw [sub2519, sub2513]
  rfl
theorem sub2521 (p : Pattern) : d402 (change p 138 none) = d47 p := by
  change (if p 133 then d401 (change p 138 none) else d399 (change p 138 none)) = d47 p
  rw [sub2520, sub2513]
  rfl
theorem sub2522 (p : Pattern) : d34 (change p 138 none) = d34 p := by
  change (if p 139 then d24 (change p 138 none) else d33 (change p 138 none)) = d34 p
  rw [sub2517, sub2497]
  rfl
theorem sub2523 (p : Pattern) : d403 (change p 138 none) = d34 p := by
  change d34 (change p 138 none) = d34 p
  exact sub2522 p
theorem sub2524 (p : Pattern) : d404 (change p 138 none) = d48 p := by
  change (if p 134 then d403 (change p 138 none) else d399 (change p 138 none)) = d48 p
  rw [sub2523, sub2513]
  rfl
theorem sub2525 (p : Pattern) : d39 (change p 138 none) = d39 p := by
  change (if p 159 then d2 (change p 138 none) else d11 (change p 138 none)) = d39 p
  rw [sub2477, sub2508]
  rfl
theorem sub2526 (p : Pattern) : d40 (change p 138 none) = d40 p := by
  change (if p 158 then d39 (change p 138 none) else d12 (change p 138 none)) = d40 p
  rw [sub2525, sub2509]
  rfl
theorem sub2527 (p : Pattern) : d41 (change p 138 none) = d41 p := by
  change (if p 139 then d40 (change p 138 none) else d38 (change p 138 none)) = d41 p
  rw [sub2526, sub2501]
  rfl
theorem sub2528 (p : Pattern) : d405 (change p 138 none) = d41 p := by
  change d41 (change p 138 none) = d41 p
  exact sub2527 p
theorem sub2529 (p : Pattern) : d406 (change p 138 none) = d49 p := by
  change (if p 134 then d400 (change p 138 none) else d405 (change p 138 none)) = d49 p
  rw [sub2519, sub2528]
  rfl
theorem sub2530 (p : Pattern) : d407 (change p 138 none) = d50 p := by
  change (if p 133 then d406 (change p 138 none) else d404 (change p 138 none)) = d50 p
  rw [sub2529, sub2524]
  rfl
theorem sub2531 (p : Pattern) : d408 (change p 138 none) = d51 p := by
  change (if p 132 then d407 (change p 138 none) else d402 (change p 138 none)) = d51 p
  rw [sub2530, sub2521]
  rfl
theorem sub2532 (p : Pattern) : d409 (change p 138 none) = d1389 p := by
  change (if p 112 then d408 (change p 138 none) else d398 (change p 138 none)) = d1389 p
  rw [sub2531, sub2505]
  rfl
theorem sub2533 (p : Pattern) : d410 (change p 138 none) = d40 p := by
  change d40 (change p 138 none) = d40 p
  exact sub2526 p
theorem sub2534 (p : Pattern) : d411 (change p 138 none) = d24 p := by
  change d24 (change p 138 none) = d24 p
  exact sub2517 p
theorem sub2535 (p : Pattern) : d412 (change p 138 none) = d1103 p := by
  change (if p 134 then d411 (change p 138 none) else d410 (change p 138 none)) = d1103 p
  rw [sub2534, sub2533]
  rfl
theorem sub2536 (p : Pattern) : d413 (change p 138 none) = d1104 p := by
  change (if p 133 then d412 (change p 138 none) else d391 (change p 138 none)) = d1104 p
  rw [sub2535, sub2490]
  rfl
theorem sub2537 (p : Pattern) : d414 (change p 138 none) = d1105 p := by
  change (if p 132 then d413 (change p 138 none) else d392 (change p 138 none)) = d1105 p
  rw [sub2536, sub2491]
  rfl
theorem sub2538 (p : Pattern) : d68 (change p 138 none) = d68 p := by
  change (if p 139 then d2 (change p 138 none) else d40 (change p 138 none)) = d68 p
  rw [sub2477, sub2526]
  rfl
theorem sub2539 (p : Pattern) : d199 (change p 138 none) = d68 p := by
  change d68 (change p 138 none) = d68 p
  exact sub2538 p
theorem sub2540 (p : Pattern) : d70 (change p 138 none) = d70 p := by
  change (if p 139 then d2 (change p 138 none) else d24 (change p 138 none)) = d70 p
  rw [sub2477, sub2517]
  rfl
theorem sub2541 (p : Pattern) : d200 (change p 138 none) = d70 p := by
  change d70 (change p 138 none) = d70 p
  exact sub2540 p
theorem sub2542 (p : Pattern) : d201 (change p 138 none) = d75 p := by
  change (if p 134 then d200 (change p 138 none) else d199 (change p 138 none)) = d75 p
  rw [sub2541, sub2539]
  rfl
theorem sub2543 (p : Pattern) : d415 (change p 138 none) = d1390 p := by
  change (if p 133 then d201 (change p 138 none) else d391 (change p 138 none)) = d1390 p
  rw [sub2542, sub2490]
  rfl
theorem sub2544 (p : Pattern) : d416 (change p 138 none) = d1391 p := by
  change (if p 132 then d415 (change p 138 none) else d392 (change p 138 none)) = d1391 p
  rw [sub2543, sub2491]
  rfl
theorem sub2545 (p : Pattern) : d417 (change p 138 none) = d1392 p := by
  change (if p 113 then d416 (change p 138 none) else d414 (change p 138 none)) = d1392 p
  rw [sub2544, sub2537]
  rfl
theorem sub2546 (p : Pattern) : d418 (change p 138 none) = d79 p := by
  change (if p 133 then d201 (change p 138 none) else d401 (change p 138 none)) = d79 p
  rw [sub2542, sub2520]
  rfl
theorem sub2547 (p : Pattern) : d419 (change p 138 none) = d80 p := by
  change (if p 132 then d418 (change p 138 none) else d402 (change p 138 none)) = d80 p
  rw [sub2546, sub2521]
  rfl
theorem sub2548 (p : Pattern) : d420 (change p 138 none) = d1393 p := by
  change (if p 112 then d419 (change p 138 none) else d417 (change p 138 none)) = d1393 p
  rw [sub2547, sub2545]
  rfl
theorem sub2549 (p : Pattern) : d421 (change p 138 none) = d1394 p := by
  change (if p 106 then d420 (change p 138 none) else d409 (change p 138 none)) = d1394 p
  rw [sub2548, sub2532]
  rfl
theorem sub2550 (p : Pattern) : d422 (change p 138 none) = d14 p := by
  change d14 (change p 138 none) = d14 p
  exact sub2511 p
theorem sub2551 (p : Pattern) : d423 (change p 138 none) = d1107 p := by
  change (if p 134 then d411 (change p 138 none) else d422 (change p 138 none)) = d1107 p
  rw [sub2534, sub2550]
  rfl
theorem sub2552 (p : Pattern) : d424 (change p 138 none) = d1108 p := by
  change (if p 133 then d423 (change p 138 none) else d422 (change p 138 none)) = d1108 p
  rw [sub2551, sub2550]
  rfl
theorem sub2553 (p : Pattern) : d425 (change p 138 none) = d1109 p := by
  change (if p 133 then d412 (change p 138 none) else d423 (change p 138 none)) = d1109 p
  rw [sub2535, sub2551]
  rfl
theorem sub2554 (p : Pattern) : d426 (change p 138 none) = d1110 p := by
  change (if p 132 then d425 (change p 138 none) else d424 (change p 138 none)) = d1110 p
  rw [sub2553, sub2552]
  rfl
theorem sub2555 (p : Pattern) : d427 (change p 138 none) = d1111 p := by
  change (if p 112 then d426 (change p 138 none) else d398 (change p 138 none)) = d1111 p
  rw [sub2554, sub2505]
  rfl
theorem sub2556 (p : Pattern) : d428 (change p 138 none) = d1112 p := by
  change (if p 133 then d2 (change p 138 none) else d423 (change p 138 none)) = d1112 p
  rw [sub2477, sub2551]
  rfl
theorem sub2557 (p : Pattern) : d429 (change p 138 none) = d1113 p := by
  change (if p 132 then d428 (change p 138 none) else d424 (change p 138 none)) = d1113 p
  rw [sub2556, sub2552]
  rfl
theorem sub2558 (p : Pattern) : d97 (change p 138 none) = d97 p := by
  change (if p 139 then d2 (change p 138 none) else d14 (change p 138 none)) = d97 p
  rw [sub2477, sub2511]
  rfl
theorem sub2559 (p : Pattern) : d430 (change p 138 none) = d97 p := by
  change d97 (change p 138 none) = d97 p
  exact sub2558 p
theorem sub2560 (p : Pattern) : d431 (change p 138 none) = d109 p := by
  change (if p 134 then d200 (change p 138 none) else d430 (change p 138 none)) = d109 p
  rw [sub2541, sub2559]
  rfl
theorem sub2561 (p : Pattern) : d432 (change p 138 none) = d110 p := by
  change (if p 133 then d431 (change p 138 none) else d430 (change p 138 none)) = d110 p
  rw [sub2560, sub2559]
  rfl
theorem sub2562 (p : Pattern) : d433 (change p 138 none) = d111 p := by
  change (if p 133 then d2 (change p 138 none) else d431 (change p 138 none)) = d111 p
  rw [sub2477, sub2560]
  rfl
theorem sub2563 (p : Pattern) : d434 (change p 138 none) = d112 p := by
  change (if p 132 then d433 (change p 138 none) else d432 (change p 138 none)) = d112 p
  rw [sub2562, sub2561]
  rfl
theorem sub2564 (p : Pattern) : d435 (change p 138 none) = d1395 p := by
  change (if p 113 then d434 (change p 138 none) else d429 (change p 138 none)) = d1395 p
  rw [sub2563, sub2557]
  rfl
theorem sub2565 (p : Pattern) : d436 (change p 138 none) = d1396 p := by
  change (if p 112 then d435 (change p 138 none) else d416 (change p 138 none)) = d1396 p
  rw [sub2564, sub2544]
  rfl
theorem sub2566 (p : Pattern) : d437 (change p 138 none) = d1397 p := by
  change (if p 106 then d436 (change p 138 none) else d427 (change p 138 none)) = d1397 p
  rw [sub2565, sub2555]
  rfl
theorem sub2567 (p : Pattern) : d438 (change p 138 none) = d1398 p := by
  change (if p 86 then d437 (change p 138 none) else d421 (change p 138 none)) = d1398 p
  rw [sub2566, sub2549]
  rfl
theorem sub2568 (p : Pattern) : d439 (change p 138 none) = d1399 p := by
  change (if p 112 then d419 (change p 138 none) else d416 (change p 138 none)) = d1399 p
  rw [sub2547, sub2544]
  rfl
theorem sub2569 (p : Pattern) : d440 (change p 138 none) = d1400 p := by
  change (if p 106 then d439 (change p 138 none) else d409 (change p 138 none)) = d1400 p
  rw [sub2568, sub2532]
  rfl
theorem sub2570 (p : Pattern) : d119 (change p 138 none) = d119 p := by
  change (if p 139 then d20 (change p 138 none) else d33 (change p 138 none)) = d119 p
  rw [sub2488, sub2497]
  rfl
theorem sub2571 (p : Pattern) : d441 (change p 138 none) = d119 p := by
  change d119 (change p 138 none) = d119 p
  exact sub2570 p
theorem sub2572 (p : Pattern) : d442 (change p 138 none) = d1401 p := by
  change (if p 134 then d441 (change p 138 none) else d389 (change p 138 none)) = d1401 p
  rw [sub2571, sub2484]
  rfl
theorem sub2573 (p : Pattern) : d443 (change p 138 none) = d1402 p := by
  change (if p 133 then d396 (change p 138 none) else d442 (change p 138 none)) = d1402 p
  rw [sub2503, sub2572]
  rfl
theorem sub2574 (p : Pattern) : d444 (change p 138 none) = d1403 p := by
  change (if p 132 then d443 (change p 138 none) else d392 (change p 138 none)) = d1403 p
  rw [sub2573, sub2491]
  rfl
theorem sub2575 (p : Pattern) : d445 (change p 138 none) = d1404 p := by
  change (if p 113 then d444 (change p 138 none) else d398 (change p 138 none)) = d1404 p
  rw [sub2574, sub2505]
  rfl
theorem sub2576 (p : Pattern) : d446 (change p 138 none) = d125 p := by
  change (if p 133 then d201 (change p 138 none) else d431 (change p 138 none)) = d125 p
  rw [sub2542, sub2560]
  rfl
theorem sub2577 (p : Pattern) : d447 (change p 138 none) = d126 p := by
  change (if p 132 then d446 (change p 138 none) else d432 (change p 138 none)) = d126 p
  rw [sub2576, sub2561]
  rfl
theorem sub2578 (p : Pattern) : d448 (change p 138 none) = d1405 p := by
  change (if p 113 then d447 (change p 138 none) else d426 (change p 138 none)) = d1405 p
  rw [sub2577, sub2554]
  rfl
theorem sub2579 (p : Pattern) : d449 (change p 138 none) = d1406 p := by
  change (if p 112 then d448 (change p 138 none) else d445 (change p 138 none)) = d1406 p
  rw [sub2578, sub2575]
  rfl
theorem sub2580 (p : Pattern) : d450 (change p 138 none) = d1407 p := by
  change (if p 113 then d419 (change p 138 none) else d416 (change p 138 none)) = d1407 p
  rw [sub2547, sub2544]
  rfl
theorem sub2581 (p : Pattern) : d451 (change p 138 none) = d130 p := by
  change (if p 113 then d2 (change p 138 none) else d434 (change p 138 none)) = d130 p
  rw [sub2477, sub2563]
  rfl
theorem sub2582 (p : Pattern) : d452 (change p 138 none) = d1408 p := by
  change (if p 112 then d451 (change p 138 none) else d450 (change p 138 none)) = d1408 p
  rw [sub2581, sub2580]
  rfl
theorem sub2583 (p : Pattern) : d453 (change p 138 none) = d1409 p := by
  change (if p 106 then d452 (change p 138 none) else d449 (change p 138 none)) = d1409 p
  rw [sub2582, sub2579]
  rfl
theorem sub2584 (p : Pattern) : d454 (change p 138 none) = d1410 p := by
  change (if p 86 then d453 (change p 138 none) else d440 (change p 138 none)) = d1410 p
  rw [sub2583, sub2569]
  rfl
theorem sub2585 (p : Pattern) : d455 (change p 138 none) = d1411 p := by
  change (if p 80 then d454 (change p 138 none) else d438 (change p 138 none)) = d1411 p
  rw [sub2584, sub2567]
  rfl
theorem sub2586 (p : Pattern) : d0 (change p 158 (some 159)) = d0 p := by
  rfl
theorem sub2587 (p : Pattern) : d2 (change p 158 (some 159)) = d2 p := by
  rfl
theorem sub2588 (p : Pattern) : d5 (change p 158 (some 159)) = d5 p := by
  change (if p 160 then d2 (change p 158 (some 159)) else d0 (change p 158 (some 159))) = d5 p
  rw [sub2587, sub2586]
  rfl
theorem sub2589 (p : Pattern) : d6 (change p 158 (some 159)) = d5 p := by
  change d5 (change p 158 (some 159)) = d5 p
  exact sub2588 p
theorem sub2590 (p : Pattern) : d538 (change p 158 (some 159)) = d5 p := by
  change d6 (change p 158 (some 159)) = d5 p
  exact sub2589 p
theorem sub2591 (p : Pattern) : d539 (change p 158 (some 159)) = d5 p := by
  change d6 (change p 158 (some 159)) = d5 p
  exact sub2589 p
theorem sub2592 (p : Pattern) : d1 (change p 158 (some 159)) = d1 p := by
  rfl
theorem sub2593 (p : Pattern) : d11 (change p 158 (some 159)) = d11 p := by
  change (if p 160 then d2 (change p 158 (some 159)) else d1 (change p 158 (some 159))) = d11 p
  rw [sub2587, sub2592]
  rfl
theorem sub2594 (p : Pattern) : d12 (change p 158 (some 159)) = d11 p := by
  change d11 (change p 158 (some 159)) = d11 p
  exact sub2593 p
theorem sub2595 (p : Pattern) : d540 (change p 158 (some 159)) = d11 p := by
  change d12 (change p 158 (some 159)) = d11 p
  exact sub2594 p
theorem sub2596 (p : Pattern) : d541 (change p 158 (some 159)) = d1413 p := by
  change (if p 139 then d540 (change p 158 (some 159)) else d539 (change p 158 (some 159))) = d1413 p
  rw [sub2595, sub2591]
  rfl
theorem sub2597 (p : Pattern) : d542 (change p 158 (some 159)) = d1414 p := by
  change (if p 138 then d541 (change p 158 (some 159)) else d538 (change p 158 (some 159))) = d1414 p
  rw [sub2596, sub2590]
  rfl
theorem sub2598 (p : Pattern) : d543 (change p 158 (some 159)) = d1414 p := by
  change (if p 138 then d541 (change p 158 (some 159)) else d539 (change p 158 (some 159))) = d1414 p
  rw [sub2596, sub2591]
  rfl
theorem sub2599 (p : Pattern) : d544 (change p 158 (some 159)) = d1414 p := by
  change (if p 134 then d543 (change p 158 (some 159)) else d542 (change p 158 (some 159))) = d1414 p
  rw [sub2598, sub2597]
  simp only [ite_self]
theorem sub2600 (p : Pattern) : d3 (change p 158 (some 159)) = d3 p := by
  change (if p 161 then d2 (change p 158 (some 159)) else d0 (change p 158 (some 159))) = d3 p
  rw [sub2587, sub2586]
  rfl
theorem sub2601 (p : Pattern) : d17 (change p 158 (some 159)) = d17 p := by
  change (if p 160 then d2 (change p 158 (some 159)) else d3 (change p 158 (some 159))) = d17 p
  rw [sub2587, sub2600]
  rfl
theorem sub2602 (p : Pattern) : d18 (change p 158 (some 159)) = d17 p := by
  change d17 (change p 158 (some 159)) = d17 p
  exact sub2601 p
theorem sub2603 (p : Pattern) : d545 (change p 158 (some 159)) = d17 p := by
  change d18 (change p 158 (some 159)) = d17 p
  exact sub2602 p
theorem sub2604 (p : Pattern) : d9 (change p 158 (some 159)) = d9 p := by
  change (if p 161 then d2 (change p 158 (some 159)) else d1 (change p 158 (some 159))) = d9 p
  rw [sub2587, sub2592]
  rfl
theorem sub2605 (p : Pattern) : d21 (change p 158 (some 159)) = d21 p := by
  change (if p 160 then d2 (change p 158 (some 159)) else d9 (change p 158 (some 159))) = d21 p
  rw [sub2587, sub2604]
  rfl
theorem sub2606 (p : Pattern) : d22 (change p 158 (some 159)) = d21 p := by
  change d21 (change p 158 (some 159)) = d21 p
  exact sub2605 p
theorem sub2607 (p : Pattern) : d546 (change p 158 (some 159)) = d21 p := by
  change d22 (change p 158 (some 159)) = d21 p
  exact sub2606 p
theorem sub2608 (p : Pattern) : d547 (change p 158 (some 159)) = d1415 p := by
  change (if p 139 then d546 (change p 158 (some 159)) else d545 (change p 158 (some 159))) = d1415 p
  rw [sub2607, sub2603]
  rfl
theorem sub2609 (p : Pattern) : d548 (change p 158 (some 159)) = d1416 p := by
  change (if p 138 then d547 (change p 158 (some 159)) else d545 (change p 158 (some 159))) = d1416 p
  rw [sub2608, sub2603]
  rfl
theorem sub2610 (p : Pattern) : d549 (change p 158 (some 159)) = d1417 p := by
  change (if p 134 then d548 (change p 158 (some 159)) else d543 (change p 158 (some 159))) = d1417 p
  rw [sub2609, sub2598]
  rfl
theorem sub2611 (p : Pattern) : d550 (change p 158 (some 159)) = d1418 p := by
  change (if p 133 then d549 (change p 158 (some 159)) else d544 (change p 158 (some 159))) = d1418 p
  rw [sub2610, sub2599]
  rfl
theorem sub2612 (p : Pattern) : d29 (change p 158 (some 159)) = d29 p := by
  change (if p 161 then d1 (change p 158 (some 159)) else d0 (change p 158 (some 159))) = d29 p
  rw [sub2592, sub2586]
  rfl
theorem sub2613 (p : Pattern) : d30 (change p 158 (some 159)) = d30 p := by
  change (if p 160 then d2 (change p 158 (some 159)) else d29 (change p 158 (some 159))) = d30 p
  rw [sub2587, sub2612]
  rfl
theorem sub2614 (p : Pattern) : d31 (change p 158 (some 159)) = d30 p := by
  change d30 (change p 158 (some 159)) = d30 p
  exact sub2613 p
theorem sub2615 (p : Pattern) : d551 (change p 158 (some 159)) = d30 p := by
  change d31 (change p 158 (some 159)) = d30 p
  exact sub2614 p
theorem sub2616 (p : Pattern) : d552 (change p 158 (some 159)) = d1419 p := by
  change (if p 139 then d546 (change p 158 (some 159)) else d551 (change p 158 (some 159))) = d1419 p
  rw [sub2607, sub2615]
  rfl
theorem sub2617 (p : Pattern) : d553 (change p 158 (some 159)) = d1420 p := by
  change (if p 138 then d552 (change p 158 (some 159)) else d551 (change p 158 (some 159))) = d1420 p
  rw [sub2616, sub2615]
  rfl
theorem sub2618 (p : Pattern) : d554 (change p 158 (some 159)) = d1421 p := by
  change (if p 134 then d553 (change p 158 (some 159)) else d542 (change p 158 (some 159))) = d1421 p
  rw [sub2617, sub2597]
  rfl
theorem sub2619 (p : Pattern) : d555 (change p 158 (some 159)) = d1422 p := by
  change (if p 133 then d549 (change p 158 (some 159)) else d554 (change p 158 (some 159))) = d1422 p
  rw [sub2610, sub2618]
  rfl
theorem sub2620 (p : Pattern) : d556 (change p 158 (some 159)) = d1423 p := by
  change (if p 132 then d555 (change p 158 (some 159)) else d550 (change p 158 (some 159))) = d1423 p
  rw [sub2619, sub2611]
  rfl
theorem sub2621 (p : Pattern) : d557 (change p 158 (some 159)) = d1424 p := by
  change (if p 134 then d547 (change p 158 (some 159)) else d541 (change p 158 (some 159))) = d1424 p
  rw [sub2608, sub2596]
  rfl
theorem sub2622 (p : Pattern) : d558 (change p 158 (some 159)) = d1425 p := by
  change (if p 133 then d557 (change p 158 (some 159)) else d541 (change p 158 (some 159))) = d1425 p
  rw [sub2621, sub2596]
  rfl
theorem sub2623 (p : Pattern) : d559 (change p 158 (some 159)) = d1426 p := by
  change (if p 134 then d552 (change p 158 (some 159)) else d541 (change p 158 (some 159))) = d1426 p
  rw [sub2616, sub2596]
  rfl
theorem sub2624 (p : Pattern) : d560 (change p 158 (some 159)) = d1427 p := by
  change (if p 133 then d557 (change p 158 (some 159)) else d559 (change p 158 (some 159))) = d1427 p
  rw [sub2621, sub2623]
  rfl
theorem sub2625 (p : Pattern) : d561 (change p 158 (some 159)) = d1428 p := by
  change (if p 132 then d560 (change p 158 (some 159)) else d558 (change p 158 (some 159))) = d1428 p
  rw [sub2624, sub2622]
  rfl
theorem sub2626 (p : Pattern) : d562 (change p 158 (some 159)) = d1429 p := by
  change (if p 139 then d2 (change p 158 (some 159)) else d539 (change p 158 (some 159))) = d1429 p
  rw [sub2587, sub2591]
  rfl
theorem sub2627 (p : Pattern) : d563 (change p 158 (some 159)) = d1430 p := by
  change (if p 138 then d562 (change p 158 (some 159)) else d541 (change p 158 (some 159))) = d1430 p
  rw [sub2626, sub2596]
  rfl
theorem sub2628 (p : Pattern) : d564 (change p 158 (some 159)) = d1431 p := by
  change (if p 139 then d2 (change p 158 (some 159)) else d545 (change p 158 (some 159))) = d1431 p
  rw [sub2587, sub2603]
  rfl
theorem sub2629 (p : Pattern) : d565 (change p 158 (some 159)) = d1432 p := by
  change (if p 138 then d564 (change p 158 (some 159)) else d547 (change p 158 (some 159))) = d1432 p
  rw [sub2628, sub2608]
  rfl
theorem sub2630 (p : Pattern) : d566 (change p 158 (some 159)) = d1433 p := by
  change (if p 134 then d565 (change p 158 (some 159)) else d563 (change p 158 (some 159))) = d1433 p
  rw [sub2629, sub2627]
  rfl
theorem sub2631 (p : Pattern) : d567 (change p 158 (some 159)) = d1434 p := by
  change (if p 133 then d566 (change p 158 (some 159)) else d563 (change p 158 (some 159))) = d1434 p
  rw [sub2630, sub2627]
  rfl
theorem sub2632 (p : Pattern) : d568 (change p 158 (some 159)) = d1435 p := by
  change (if p 139 then d2 (change p 158 (some 159)) else d551 (change p 158 (some 159))) = d1435 p
  rw [sub2587, sub2615]
  rfl
theorem sub2633 (p : Pattern) : d569 (change p 158 (some 159)) = d1436 p := by
  change (if p 138 then d568 (change p 158 (some 159)) else d552 (change p 158 (some 159))) = d1436 p
  rw [sub2632, sub2616]
  rfl
theorem sub2634 (p : Pattern) : d570 (change p 158 (some 159)) = d1437 p := by
  change (if p 134 then d569 (change p 158 (some 159)) else d563 (change p 158 (some 159))) = d1437 p
  rw [sub2633, sub2627]
  rfl
theorem sub2635 (p : Pattern) : d571 (change p 158 (some 159)) = d1438 p := by
  change (if p 133 then d566 (change p 158 (some 159)) else d570 (change p 158 (some 159))) = d1438 p
  rw [sub2630, sub2634]
  rfl
theorem sub2636 (p : Pattern) : d572 (change p 158 (some 159)) = d1439 p := by
  change (if p 132 then d571 (change p 158 (some 159)) else d567 (change p 158 (some 159))) = d1439 p
  rw [sub2635, sub2631]
  rfl
theorem sub2637 (p : Pattern) : d573 (change p 158 (some 159)) = d1440 p := by
  change (if p 113 then d572 (change p 158 (some 159)) else d561 (change p 158 (some 159))) = d1440 p
  rw [sub2636, sub2625]
  rfl
theorem sub2638 (p : Pattern) : d574 (change p 158 (some 159)) = d1441 p := by
  change (if p 112 then d573 (change p 158 (some 159)) else d556 (change p 158 (some 159))) = d1441 p
  rw [sub2637, sub2620]
  rfl
theorem sub2639 (p : Pattern) : d575 (change p 158 (some 159)) = d1417 p := by
  change (if p 134 then d548 (change p 158 (some 159)) else d542 (change p 158 (some 159))) = d1417 p
  rw [sub2609, sub2597]
  rfl
end NetHack.Sokoban32Refined
