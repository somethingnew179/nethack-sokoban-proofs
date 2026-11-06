/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions20
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2520 (p : Pattern) : d28 (change p 115 (some 116)) = d28 p := by
  change (if p 162 then d27 (change p 115 (some 116)) else d21 (change p 115 (some 116))) = d28 p
  rw [sub2519, sub2512]
  rfl
theorem sub2521 (p : Pattern) : d29 (change p 115 (some 116)) = d29 p := by
  change (if p 161 then d28 (change p 115 (some 116)) else d22 (change p 115 (some 116))) = d29 p
  rw [sub2520, sub2513]
  rfl
theorem sub2522 (p : Pattern) : d2 (change p 115 (some 116)) = d2 p := by
  rfl
theorem sub2523 (p : Pattern) : d30 (change p 115 (some 116)) = d30 p := by
  change (if p 247 then d12 (change p 115 (some 116)) else d2 (change p 115 (some 116))) = d30 p
  rw [sub2502, sub2522]
  rfl
theorem sub2524 (p : Pattern) : d31 (change p 115 (some 116)) = d31 p := by
  change (if p 246 then d30 (change p 115 (some 116)) else d2 (change p 115 (some 116))) = d31 p
  rw [sub2523, sub2522]
  rfl
theorem sub2525 (p : Pattern) : d32 (change p 115 (some 116)) = d32 p := by
  change (if p 204 then d12 (change p 115 (some 116)) else d31 (change p 115 (some 116))) = d32 p
  rw [sub2502, sub2524]
  rfl
theorem sub2526 (p : Pattern) : d53 (change p 115 (some 116)) = d53 p := by
  change (if p 182 then d32 (change p 115 (some 116)) else d31 (change p 115 (some 116))) = d53 p
  rw [sub2525, sub2524]
  rfl
theorem sub2527 (p : Pattern) : d6 (change p 115 (some 116)) = d6 p := by
  rfl
theorem sub2528 (p : Pattern) : d34 (change p 115 (some 116)) = d34 p := by
  change (if p 247 then d12 (change p 115 (some 116)) else d6 (change p 115 (some 116))) = d34 p
  rw [sub2502, sub2527]
  rfl
theorem sub2529 (p : Pattern) : d35 (change p 115 (some 116)) = d35 p := by
  change (if p 246 then d34 (change p 115 (some 116)) else d6 (change p 115 (some 116))) = d35 p
  rw [sub2528, sub2527]
  rfl
theorem sub2530 (p : Pattern) : d36 (change p 115 (some 116)) = d36 p := by
  change (if p 204 then d12 (change p 115 (some 116)) else d35 (change p 115 (some 116))) = d36 p
  rw [sub2502, sub2529]
  rfl
theorem sub2531 (p : Pattern) : d78 (change p 115 (some 116)) = d78 p := by
  change (if p 182 then d36 (change p 115 (some 116)) else d35 (change p 115 (some 116))) = d78 p
  rw [sub2530, sub2529]
  rfl
theorem sub2532 (p : Pattern) : d79 (change p 115 (some 116)) = d79 p := by
  change (if p 163 then d78 (change p 115 (some 116)) else d53 (change p 115 (some 116))) = d79 p
  rw [sub2531, sub2526]
  rfl
theorem sub2533 (p : Pattern) : d11 (change p 115 (some 116)) = d11 p := by
  rfl
theorem sub2534 (p : Pattern) : d39 (change p 115 (some 116)) = d39 p := by
  change (if p 247 then d12 (change p 115 (some 116)) else d11 (change p 115 (some 116))) = d39 p
  rw [sub2502, sub2533]
  rfl
theorem sub2535 (p : Pattern) : d40 (change p 115 (some 116)) = d40 p := by
  change (if p 246 then d39 (change p 115 (some 116)) else d11 (change p 115 (some 116))) = d40 p
  rw [sub2534, sub2533]
  rfl
theorem sub2536 (p : Pattern) : d41 (change p 115 (some 116)) = d41 p := by
  change (if p 204 then d12 (change p 115 (some 116)) else d40 (change p 115 (some 116))) = d41 p
  rw [sub2502, sub2535]
  rfl
theorem sub2537 (p : Pattern) : d62 (change p 115 (some 116)) = d62 p := by
  change (if p 182 then d41 (change p 115 (some 116)) else d40 (change p 115 (some 116))) = d62 p
  rw [sub2536, sub2535]
  rfl
theorem sub2538 (p : Pattern) : d63 (change p 115 (some 116)) = d63 p := by
  change (if p 163 then d12 (change p 115 (some 116)) else d62 (change p 115 (some 116))) = d63 p
  rw [sub2502, sub2537]
  rfl
theorem sub2539 (p : Pattern) : d80 (change p 115 (some 116)) = d80 p := by
  change (if p 162 then d63 (change p 115 (some 116)) else d79 (change p 115 (some 116))) = d80 p
  rw [sub2538, sub2532]
  rfl
theorem sub2540 (p : Pattern) : d81 (change p 115 (some 116)) = d81 p := by
  change (if p 161 then d12 (change p 115 (some 116)) else d80 (change p 115 (some 116))) = d81 p
  rw [sub2502, sub2539]
  rfl
theorem sub2541 (p : Pattern) : d82 (change p 115 (some 116)) = d82 p := by
  change (if p 160 then d81 (change p 115 (some 116)) else d29 (change p 115 (some 116))) = d82 p
  rw [sub2540, sub2521]
  rfl
theorem sub2542 (p : Pattern) : d54 (change p 115 (some 116)) = d54 p := by
  change (if p 163 then d53 (change p 115 (some 116)) else d16 (change p 115 (some 116))) = d54 p
  rw [sub2526, sub2506]
  rfl
theorem sub2543 (p : Pattern) : d55 (change p 115 (some 116)) = d55 p := by
  change (if p 163 then d26 (change p 115 (some 116)) else d20 (change p 115 (some 116))) = d55 p
  rw [sub2518, sub2511]
  rfl
theorem sub2544 (p : Pattern) : d56 (change p 115 (some 116)) = d56 p := by
  change (if p 162 then d55 (change p 115 (some 116)) else d54 (change p 115 (some 116))) = d56 p
  rw [sub2543, sub2542]
  rfl
theorem sub2545 (p : Pattern) : d10 (change p 115 (some 116)) = d10 p := by
  rfl
theorem sub2546 (p : Pattern) : d57 (change p 115 (some 116)) = d57 p := by
  change (if p 247 then d12 (change p 115 (some 116)) else d10 (change p 115 (some 116))) = d57 p
  rw [sub2502, sub2545]
  rfl
theorem sub2547 (p : Pattern) : d58 (change p 115 (some 116)) = d58 p := by
  change (if p 246 then d57 (change p 115 (some 116)) else d10 (change p 115 (some 116))) = d58 p
  rw [sub2546, sub2545]
  rfl
theorem sub2548 (p : Pattern) : d59 (change p 115 (some 116)) = d59 p := by
  change (if p 204 then d12 (change p 115 (some 116)) else d58 (change p 115 (some 116))) = d59 p
  rw [sub2502, sub2547]
  rfl
theorem sub2549 (p : Pattern) : d60 (change p 115 (some 116)) = d60 p := by
  change (if p 182 then d59 (change p 115 (some 116)) else d58 (change p 115 (some 116))) = d60 p
  rw [sub2548, sub2547]
  rfl
theorem sub2550 (p : Pattern) : d61 (change p 115 (some 116)) = d61 p := by
  change (if p 163 then d60 (change p 115 (some 116)) else d20 (change p 115 (some 116))) = d61 p
  rw [sub2549, sub2511]
  rfl
theorem sub2551 (p : Pattern) : d64 (change p 115 (some 116)) = d64 p := by
  change (if p 162 then d63 (change p 115 (some 116)) else d61 (change p 115 (some 116))) = d64 p
  rw [sub2538, sub2550]
  rfl
theorem sub2552 (p : Pattern) : d65 (change p 115 (some 116)) = d65 p := by
  change (if p 161 then d64 (change p 115 (some 116)) else d56 (change p 115 (some 116))) = d65 p
  rw [sub2551, sub2544]
  rfl
theorem sub2553 (p : Pattern) : d83 (change p 115 (some 116)) = d83 p := by
  change (if p 163 then d12 (change p 115 (some 116)) else d78 (change p 115 (some 116))) = d83 p
  rw [sub2502, sub2531]
  rfl
theorem sub2554 (p : Pattern) : d84 (change p 115 (some 116)) = d84 p := by
  change (if p 162 then d12 (change p 115 (some 116)) else d83 (change p 115 (some 116))) = d84 p
  rw [sub2502, sub2553]
  rfl
theorem sub2555 (p : Pattern) : d85 (change p 115 (some 116)) = d85 p := by
  change (if p 161 then d12 (change p 115 (some 116)) else d84 (change p 115 (some 116))) = d85 p
  rw [sub2502, sub2554]
  rfl
theorem sub2556 (p : Pattern) : d86 (change p 115 (some 116)) = d86 p := by
  change (if p 160 then d85 (change p 115 (some 116)) else d65 (change p 115 (some 116))) = d86 p
  rw [sub2555, sub2552]
  rfl
theorem sub2557 (p : Pattern) : d87 (change p 115 (some 116)) = d87 p := by
  change (if p 141 then d86 (change p 115 (some 116)) else d82 (change p 115 (some 116))) = d87 p
  rw [sub2556, sub2541]
  rfl
theorem sub2558 (p : Pattern) : d89 (change p 115 (some 116)) = d89 p := by
  change (if p 163 then d62 (change p 115 (some 116)) else d26 (change p 115 (some 116))) = d89 p
  rw [sub2537, sub2518]
  rfl
theorem sub2559 (p : Pattern) : d90 (change p 115 (some 116)) = d90 p := by
  change (if p 162 then d63 (change p 115 (some 116)) else d89 (change p 115 (some 116))) = d90 p
  rw [sub2538, sub2558]
  rfl
theorem sub2560 (p : Pattern) : d91 (change p 115 (some 116)) = d91 p := by
  change (if p 162 then d12 (change p 115 (some 116)) else d63 (change p 115 (some 116))) = d91 p
  rw [sub2502, sub2538]
  rfl
theorem sub2561 (p : Pattern) : d92 (change p 115 (some 116)) = d92 p := by
  change (if p 161 then d91 (change p 115 (some 116)) else d90 (change p 115 (some 116))) = d92 p
  rw [sub2560, sub2559]
  rfl
theorem sub2562 (p : Pattern) : d93 (change p 115 (some 116)) = d93 p := by
  change (if p 161 then d12 (change p 115 (some 116)) else d91 (change p 115 (some 116))) = d93 p
  rw [sub2502, sub2560]
  rfl
theorem sub2563 (p : Pattern) : d94 (change p 115 (some 116)) = d94 p := by
  change (if p 160 then d93 (change p 115 (some 116)) else d92 (change p 115 (some 116))) = d94 p
  rw [sub2562, sub2561]
  rfl
theorem sub2564 (p : Pattern) : d95 (change p 115 (some 116)) = d95 p := by
  change (if p 160 then d12 (change p 115 (some 116)) else d93 (change p 115 (some 116))) = d95 p
  rw [sub2502, sub2562]
  rfl
theorem sub2565 (p : Pattern) : d96 (change p 115 (some 116)) = d96 p := by
  change (if p 141 then d95 (change p 115 (some 116)) else d94 (change p 115 (some 116))) = d96 p
  rw [sub2564, sub2563]
  rfl
theorem sub2566 (p : Pattern) : d97 (change p 115 (some 116)) = d97 p := by
  change (if p 138 then d96 (change p 115 (some 116)) else d87 (change p 115 (some 116))) = d97 p
  rw [sub2565, sub2557]
  rfl
theorem sub2567 (p : Pattern) : d98 (change p 115 (some 116)) = d97 p := by
  change d97 (change p 115 (some 116)) = d97 p
  exact sub2566 p
theorem sub2568 (p : Pattern) : d489 (change p 115 (some 116)) = d97 p := by
  change d98 (change p 115 (some 116)) = d97 p
  exact sub2567 p
theorem sub2569 (p : Pattern) : d490 (change p 115 (some 116)) = d97 p := by
  change d98 (change p 115 (some 116)) = d97 p
  exact sub2567 p
theorem sub2570 (p : Pattern) : d491 (change p 115 (some 116)) = d97 p := by
  change (if p 71 then d490 (change p 115 (some 116)) else d489 (change p 115 (some 116))) = d97 p
  rw [sub2569, sub2568]
  simp only [ite_self]
theorem sub2571 (p : Pattern) : d1 (change p 115 (some 116)) = d1 p := by
  rfl
theorem sub2572 (p : Pattern) : d102 (change p 115 (some 116)) = d102 p := by
  change (if p 247 then d12 (change p 115 (some 116)) else d1 (change p 115 (some 116))) = d102 p
  rw [sub2502, sub2571]
  rfl
theorem sub2573 (p : Pattern) : d103 (change p 115 (some 116)) = d103 p := by
  change (if p 246 then d102 (change p 115 (some 116)) else d1 (change p 115 (some 116))) = d103 p
  rw [sub2572, sub2571]
  rfl
theorem sub2574 (p : Pattern) : d104 (change p 115 (some 116)) = d104 p := by
  change (if p 204 then d12 (change p 115 (some 116)) else d103 (change p 115 (some 116))) = d104 p
  rw [sub2502, sub2573]
  rfl
theorem sub2575 (p : Pattern) : d105 (change p 115 (some 116)) = d105 p := by
  change (if p 182 then d104 (change p 115 (some 116)) else d103 (change p 115 (some 116))) = d105 p
  rw [sub2574, sub2573]
  rfl
theorem sub2576 (p : Pattern) : d5 (change p 115 (some 116)) = d5 p := by
  rfl
theorem sub2577 (p : Pattern) : d106 (change p 115 (some 116)) = d106 p := by
  change (if p 247 then d12 (change p 115 (some 116)) else d5 (change p 115 (some 116))) = d106 p
  rw [sub2502, sub2576]
  rfl
theorem sub2578 (p : Pattern) : d107 (change p 115 (some 116)) = d107 p := by
  change (if p 246 then d106 (change p 115 (some 116)) else d5 (change p 115 (some 116))) = d107 p
  rw [sub2577, sub2576]
  rfl
theorem sub2579 (p : Pattern) : d108 (change p 115 (some 116)) = d108 p := by
  change (if p 204 then d12 (change p 115 (some 116)) else d107 (change p 115 (some 116))) = d108 p
  rw [sub2502, sub2578]
  rfl
theorem sub2580 (p : Pattern) : d109 (change p 115 (some 116)) = d109 p := by
  change (if p 182 then d108 (change p 115 (some 116)) else d107 (change p 115 (some 116))) = d109 p
  rw [sub2579, sub2578]
  rfl
theorem sub2581 (p : Pattern) : d110 (change p 115 (some 116)) = d110 p := by
  change (if p 163 then d109 (change p 115 (some 116)) else d105 (change p 115 (some 116))) = d110 p
  rw [sub2580, sub2575]
  rfl
theorem sub2582 (p : Pattern) : d111 (change p 115 (some 116)) = d111 p := by
  change (if p 162 then d110 (change p 115 (some 116)) else d105 (change p 115 (some 116))) = d111 p
  rw [sub2581, sub2575]
  rfl
theorem sub2583 (p : Pattern) : d112 (change p 115 (some 116)) = d112 p := by
  change (if p 163 then d12 (change p 115 (some 116)) else d60 (change p 115 (some 116))) = d112 p
  rw [sub2502, sub2549]
  rfl
theorem sub2584 (p : Pattern) : d113 (change p 115 (some 116)) = d113 p := by
  change (if p 162 then d112 (change p 115 (some 116)) else d110 (change p 115 (some 116))) = d113 p
  rw [sub2583, sub2581]
  rfl
theorem sub2585 (p : Pattern) : d114 (change p 115 (some 116)) = d114 p := by
  change (if p 161 then d113 (change p 115 (some 116)) else d111 (change p 115 (some 116))) = d114 p
  rw [sub2584, sub2582]
  rfl
theorem sub2586 (p : Pattern) : d3 (change p 115 (some 116)) = d3 p := by
  rfl
theorem sub2587 (p : Pattern) : d115 (change p 115 (some 116)) = d115 p := by
  change (if p 247 then d12 (change p 115 (some 116)) else d3 (change p 115 (some 116))) = d115 p
  rw [sub2502, sub2586]
  rfl
theorem sub2588 (p : Pattern) : d116 (change p 115 (some 116)) = d116 p := by
  change (if p 246 then d115 (change p 115 (some 116)) else d3 (change p 115 (some 116))) = d116 p
  rw [sub2587, sub2586]
  rfl
theorem sub2589 (p : Pattern) : d117 (change p 115 (some 116)) = d117 p := by
  change (if p 204 then d12 (change p 115 (some 116)) else d116 (change p 115 (some 116))) = d117 p
  rw [sub2502, sub2588]
  rfl
theorem sub2590 (p : Pattern) : d132 (change p 115 (some 116)) = d132 p := by
  change (if p 182 then d117 (change p 115 (some 116)) else d116 (change p 115 (some 116))) = d132 p
  rw [sub2589, sub2588]
  rfl
theorem sub2591 (p : Pattern) : d7 (change p 115 (some 116)) = d7 p := by
  rfl
theorem sub2592 (p : Pattern) : d119 (change p 115 (some 116)) = d119 p := by
  change (if p 247 then d12 (change p 115 (some 116)) else d7 (change p 115 (some 116))) = d119 p
  rw [sub2502, sub2591]
  rfl
theorem sub2593 (p : Pattern) : d120 (change p 115 (some 116)) = d120 p := by
  change (if p 246 then d119 (change p 115 (some 116)) else d7 (change p 115 (some 116))) = d120 p
  rw [sub2592, sub2591]
  rfl
theorem sub2594 (p : Pattern) : d121 (change p 115 (some 116)) = d121 p := by
  change (if p 204 then d12 (change p 115 (some 116)) else d120 (change p 115 (some 116))) = d121 p
  rw [sub2502, sub2593]
  rfl
theorem sub2595 (p : Pattern) : d148 (change p 115 (some 116)) = d148 p := by
  change (if p 182 then d121 (change p 115 (some 116)) else d120 (change p 115 (some 116))) = d148 p
  rw [sub2594, sub2593]
  rfl
theorem sub2596 (p : Pattern) : d149 (change p 115 (some 116)) = d149 p := by
  change (if p 163 then d148 (change p 115 (some 116)) else d132 (change p 115 (some 116))) = d149 p
  rw [sub2595, sub2590]
  rfl
theorem sub2597 (p : Pattern) : d150 (change p 115 (some 116)) = d150 p := by
  change (if p 162 then d12 (change p 115 (some 116)) else d149 (change p 115 (some 116))) = d150 p
  rw [sub2502, sub2596]
  rfl
theorem sub2598 (p : Pattern) : d151 (change p 115 (some 116)) = d151 p := by
  change (if p 161 then d12 (change p 115 (some 116)) else d150 (change p 115 (some 116))) = d151 p
  rw [sub2502, sub2597]
  rfl
theorem sub2599 (p : Pattern) : d152 (change p 115 (some 116)) = d152 p := by
  change (if p 160 then d151 (change p 115 (some 116)) else d114 (change p 115 (some 116))) = d152 p
  rw [sub2598, sub2585]
  rfl
theorem sub2600 (p : Pattern) : d133 (change p 115 (some 116)) = d133 p := by
  change (if p 163 then d132 (change p 115 (some 116)) else d105 (change p 115 (some 116))) = d133 p
  rw [sub2590, sub2575]
  rfl
theorem sub2601 (p : Pattern) : d134 (change p 115 (some 116)) = d134 p := by
  change (if p 163 then d60 (change p 115 (some 116)) else d109 (change p 115 (some 116))) = d134 p
  rw [sub2549, sub2580]
  rfl
theorem sub2602 (p : Pattern) : d135 (change p 115 (some 116)) = d135 p := by
  change (if p 162 then d134 (change p 115 (some 116)) else d133 (change p 115 (some 116))) = d135 p
  rw [sub2601, sub2600]
  rfl
theorem sub2603 (p : Pattern) : d136 (change p 115 (some 116)) = d136 p := by
  change (if p 163 then d62 (change p 115 (some 116)) else d109 (change p 115 (some 116))) = d136 p
  rw [sub2537, sub2580]
  rfl
theorem sub2604 (p : Pattern) : d137 (change p 115 (some 116)) = d137 p := by
  change (if p 162 then d12 (change p 115 (some 116)) else d136 (change p 115 (some 116))) = d137 p
  rw [sub2502, sub2603]
  rfl
theorem sub2605 (p : Pattern) : d138 (change p 115 (some 116)) = d138 p := by
  change (if p 161 then d137 (change p 115 (some 116)) else d135 (change p 115 (some 116))) = d138 p
  rw [sub2604, sub2602]
  rfl
theorem sub2606 (p : Pattern) : d153 (change p 115 (some 116)) = d153 p := by
  change (if p 163 then d12 (change p 115 (some 116)) else d148 (change p 115 (some 116))) = d153 p
  rw [sub2502, sub2595]
  rfl
theorem sub2607 (p : Pattern) : d154 (change p 115 (some 116)) = d154 p := by
  change (if p 162 then d12 (change p 115 (some 116)) else d153 (change p 115 (some 116))) = d154 p
  rw [sub2502, sub2606]
  rfl
theorem sub2608 (p : Pattern) : d155 (change p 115 (some 116)) = d155 p := by
  change (if p 161 then d12 (change p 115 (some 116)) else d154 (change p 115 (some 116))) = d155 p
  rw [sub2502, sub2607]
  rfl
theorem sub2609 (p : Pattern) : d156 (change p 115 (some 116)) = d156 p := by
  change (if p 160 then d155 (change p 115 (some 116)) else d138 (change p 115 (some 116))) = d156 p
  rw [sub2608, sub2605]
  rfl
theorem sub2610 (p : Pattern) : d157 (change p 115 (some 116)) = d157 p := by
  change (if p 141 then d156 (change p 115 (some 116)) else d152 (change p 115 (some 116))) = d157 p
  rw [sub2609, sub2599]
  rfl
theorem sub2611 (p : Pattern) : d159 (change p 115 (some 116)) = d159 p := by
  change (if p 162 then d12 (change p 115 (some 116)) else d112 (change p 115 (some 116))) = d159 p
  rw [sub2502, sub2583]
  rfl
theorem sub2612 (p : Pattern) : d160 (change p 115 (some 116)) = d160 p := by
  change (if p 161 then d12 (change p 115 (some 116)) else d159 (change p 115 (some 116))) = d160 p
  rw [sub2502, sub2611]
  rfl
theorem sub2613 (p : Pattern) : d161 (change p 115 (some 116)) = d161 p := by
  change (if p 160 then d12 (change p 115 (some 116)) else d160 (change p 115 (some 116))) = d161 p
  rw [sub2502, sub2612]
  rfl
theorem sub2614 (p : Pattern) : d162 (change p 115 (some 116)) = d162 p := by
  change (if p 141 then d12 (change p 115 (some 116)) else d161 (change p 115 (some 116))) = d162 p
  rw [sub2502, sub2613]
  rfl
theorem sub2615 (p : Pattern) : d163 (change p 115 (some 116)) = d163 p := by
  change (if p 138 then d162 (change p 115 (some 116)) else d157 (change p 115 (some 116))) = d163 p
  rw [sub2614, sub2610]
  rfl
theorem sub2616 (p : Pattern) : d164 (change p 115 (some 116)) = d163 p := by
  change d163 (change p 115 (some 116)) = d163 p
  exact sub2615 p
theorem sub2617 (p : Pattern) : d492 (change p 115 (some 116)) = d163 p := by
  change d164 (change p 115 (some 116)) = d163 p
  exact sub2616 p
theorem sub2618 (p : Pattern) : d493 (change p 115 (some 116)) = d4104 p := by
  change (if p 71 then d492 (change p 115 (some 116)) else d489 (change p 115 (some 116))) = d4104 p
  rw [sub2617, sub2568]
  rfl
theorem sub2619 (p : Pattern) : d494 (change p 115 (some 116)) = d4105 p := by
  change (if p 49 then d493 (change p 115 (some 116)) else d491 (change p 115 (some 116))) = d4105 p
  rw [sub2618, sub2570]
  rfl
theorem sub2620 (p : Pattern) : d211 (change p 115 (some 116)) = d211 p := by
  change (if p 163 then d12 (change p 115 (some 116)) else d109 (change p 115 (some 116))) = d211 p
  rw [sub2502, sub2580]
  rfl
theorem sub2621 (p : Pattern) : d212 (change p 115 (some 116)) = d212 p := by
  change (if p 162 then d211 (change p 115 (some 116)) else d133 (change p 115 (some 116))) = d212 p
  rw [sub2620, sub2600]
  rfl
theorem sub2622 (p : Pattern) : d213 (change p 115 (some 116)) = d213 p := by
  change (if p 162 then d12 (change p 115 (some 116)) else d211 (change p 115 (some 116))) = d213 p
  rw [sub2502, sub2620]
  rfl
theorem sub2623 (p : Pattern) : d214 (change p 115 (some 116)) = d214 p := by
  change (if p 161 then d213 (change p 115 (some 116)) else d212 (change p 115 (some 116))) = d214 p
  rw [sub2622, sub2621]
  rfl
theorem sub2624 (p : Pattern) : d221 (change p 115 (some 116)) = d221 p := by
  change (if p 160 then d155 (change p 115 (some 116)) else d214 (change p 115 (some 116))) = d221 p
  rw [sub2608, sub2623]
  rfl
theorem sub2625 (p : Pattern) : d222 (change p 115 (some 116)) = d222 p := by
  change (if p 141 then d221 (change p 115 (some 116)) else d152 (change p 115 (some 116))) = d222 p
  rw [sub2624, sub2599]
  rfl
theorem sub2626 (p : Pattern) : d224 (change p 115 (some 116)) = d224 p := by
  change (if p 138 then d162 (change p 115 (some 116)) else d222 (change p 115 (some 116))) = d224 p
  rw [sub2614, sub2625]
  rfl
theorem sub2627 (p : Pattern) : d225 (change p 115 (some 116)) = d224 p := by
  change d224 (change p 115 (some 116)) = d224 p
  exact sub2626 p
theorem sub2628 (p : Pattern) : d495 (change p 115 (some 116)) = d224 p := by
  change d225 (change p 115 (some 116)) = d224 p
  exact sub2627 p
theorem sub2629 (p : Pattern) : d496 (change p 115 (some 116)) = d4106 p := by
  change (if p 71 then d495 (change p 115 (some 116)) else d489 (change p 115 (some 116))) = d4106 p
  rw [sub2628, sub2568]
  rfl
theorem sub2630 (p : Pattern) : d497 (change p 115 (some 116)) = d4107 p := by
  change (if p 49 then d496 (change p 115 (some 116)) else d491 (change p 115 (some 116))) = d4107 p
  rw [sub2629, sub2570]
  rfl
theorem sub2631 (p : Pattern) : d498 (change p 115 (some 116)) = d4108 p := by
  change (if p 48 then d497 (change p 115 (some 116)) else d494 (change p 115 (some 116))) = d4108 p
  rw [sub2630, sub2619]
  rfl
theorem sub2632 (p : Pattern) : d268 (change p 10000 (some 71)) = d268 p := by
  change (if p 204 then d116 (change p 10000 (some 71)) else d103 (change p 10000 (some 71))) = d268 p
  rw [sub1644, sub1629]
  rfl
theorem sub2633 (p : Pattern) : d269 (change p 10000 (some 71)) = d269 p := by
  change (if p 182 then d117 (change p 10000 (some 71)) else d268 (change p 10000 (some 71))) = d269 p
  rw [sub1645, sub2632]
  rfl
theorem sub2634 (p : Pattern) : d270 (change p 10000 (some 71)) = d270 p := by
  change (if p 182 then d121 (change p 10000 (some 71)) else d268 (change p 10000 (some 71))) = d270 p
  rw [sub1650, sub2632]
  rfl
theorem sub2635 (p : Pattern) : d271 (change p 10000 (some 71)) = d271 p := by
  change (if p 163 then d270 (change p 10000 (some 71)) else d269 (change p 10000 (some 71))) = d271 p
  rw [sub2634, sub2633]
  rfl
theorem sub2636 (p : Pattern) : d272 (change p 10000 (some 71)) = d272 p := by
  change (if p 182 then d12 (change p 10000 (some 71)) else d268 (change p 10000 (some 71))) = d272 p
  rw [sub1531, sub2632]
  rfl
theorem sub2637 (p : Pattern) : d273 (change p 10000 (some 71)) = d273 p := by
  change (if p 204 then d120 (change p 10000 (some 71)) else d107 (change p 10000 (some 71))) = d273 p
  rw [sub1649, sub1634]
  rfl
theorem sub2638 (p : Pattern) : d274 (change p 10000 (some 71)) = d274 p := by
  change (if p 182 then d12 (change p 10000 (some 71)) else d273 (change p 10000 (some 71))) = d274 p
  rw [sub1531, sub2637]
  rfl
theorem sub2639 (p : Pattern) : d275 (change p 10000 (some 71)) = d275 p := by
  change (if p 163 then d274 (change p 10000 (some 71)) else d272 (change p 10000 (some 71))) = d275 p
  rw [sub2638, sub2636]
  rfl
end NetHack.Sokoban22Refined85
