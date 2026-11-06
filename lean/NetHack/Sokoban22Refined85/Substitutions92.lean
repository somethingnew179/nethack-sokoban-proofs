/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions91
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub11040 (p : Pattern) : d2550 (change p 225 (some 224)) = d6062 p := by
  change (if p 163 then d2549 (change p 225 (some 224)) else d2544 (change p 225 (some 224))) = d6062 p
  rw [sub11039, sub11031]
  rfl
theorem sub11041 (p : Pattern) : d327 (change p 225 (some 224)) = d327 p := by
  change (if p 246 then d12 (change p 225 (some 224)) else d39 (change p 225 (some 224))) = d327 p
  rw [sub10962, sub11017]
  rfl
theorem sub11042 (p : Pattern) : d332 (change p 225 (some 224)) = d327 p := by
  change d327 (change p 225 (some 224)) = d327 p
  exact sub11041 p
theorem sub11043 (p : Pattern) : d2552 (change p 225 (some 224)) = d327 p := by
  change d332 (change p 225 (some 224)) = d327 p
  exact sub11042 p
theorem sub11044 (p : Pattern) : d2553 (change p 225 (some 224)) = d6063 p := by
  change (if p 204 then d12 (change p 225 (some 224)) else d2552 (change p 225 (some 224))) = d6063 p
  rw [sub10962, sub11043]
  rfl
theorem sub11045 (p : Pattern) : d2554 (change p 225 (some 224)) = d6064 p := by
  change (if p 182 then d2553 (change p 225 (some 224)) else d2518 (change p 225 (some 224))) = d6064 p
  rw [sub11044, sub10986]
  rfl
theorem sub11046 (p : Pattern) : d2555 (change p 225 (some 224)) = d6065 p := by
  change (if p 182 then d12 (change p 225 (some 224)) else d2523 (change p 225 (some 224))) = d6065 p
  rw [sub10962, sub10996]
  rfl
theorem sub11047 (p : Pattern) : d2556 (change p 225 (some 224)) = d6066 p := by
  change (if p 163 then d2555 (change p 225 (some 224)) else d2554 (change p 225 (some 224))) = d6066 p
  rw [sub11046, sub11045]
  rfl
theorem sub11048 (p : Pattern) : d2557 (change p 225 (some 224)) = d6067 p := by
  change (if p 162 then d2556 (change p 225 (some 224)) else d2550 (change p 225 (some 224))) = d6067 p
  rw [sub11047, sub11040]
  rfl
theorem sub11049 (p : Pattern) : d2558 (change p 225 (some 224)) = d6068 p := by
  change (if p 182 then d12 (change p 225 (some 224)) else d2518 (change p 225 (some 224))) = d6068 p
  rw [sub10962, sub10986]
  rfl
theorem sub11050 (p : Pattern) : d2559 (change p 225 (some 224)) = d6069 p := by
  change (if p 163 then d2555 (change p 225 (some 224)) else d2558 (change p 225 (some 224))) = d6069 p
  rw [sub11046, sub11049]
  rfl
theorem sub11051 (p : Pattern) : d2560 (change p 225 (some 224)) = d6070 p := by
  change (if p 182 then d12 (change p 225 (some 224)) else d2532 (change p 225 (some 224))) = d6070 p
  rw [sub10962, sub11014]
  rfl
theorem sub11052 (p : Pattern) : d2561 (change p 225 (some 224)) = d6071 p := by
  change (if p 163 then d12 (change p 225 (some 224)) else d2560 (change p 225 (some 224))) = d6071 p
  rw [sub10962, sub11051]
  rfl
theorem sub11053 (p : Pattern) : d2562 (change p 225 (some 224)) = d6072 p := by
  change (if p 162 then d2561 (change p 225 (some 224)) else d2559 (change p 225 (some 224))) = d6072 p
  rw [sub11052, sub11050]
  rfl
theorem sub11054 (p : Pattern) : d2563 (change p 225 (some 224)) = d6073 p := by
  change (if p 161 then d2562 (change p 225 (some 224)) else d2557 (change p 225 (some 224))) = d6073 p
  rw [sub11053, sub11048]
  rfl
theorem sub11055 (p : Pattern) : d2564 (change p 225 (some 224)) = d6074 p := by
  change (if p 160 then d2563 (change p 225 (some 224)) else d2539 (change p 225 (some 224))) = d6074 p
  rw [sub11054, sub11025]
  rfl
theorem sub11056 (p : Pattern) : d2566 (change p 225 (some 224)) = d14 p := by
  change d2504 (change p 225 (some 224)) = d14 p
  exact sub10965 p
theorem sub11057 (p : Pattern) : d2567 (change p 225 (some 224)) = d6044 p := by
  change (if p 204 then d2507 (change p 225 (some 224)) else d2566 (change p 225 (some 224))) = d6044 p
  rw [sub10972, sub11056]
  rfl
theorem sub11058 (p : Pattern) : d2568 (change p 225 (some 224)) = d6046 p := by
  change (if p 182 then d2511 (change p 225 (some 224)) else d2567 (change p 225 (some 224))) = d6046 p
  rw [sub10980, sub11057]
  rfl
theorem sub11059 (p : Pattern) : d31 (change p 225 (some 224)) = d31 p := by
  change (if p 246 then d30 (change p 225 (some 224)) else d2 (change p 225 (some 224))) = d31 p
  rw [sub10976, sub10974]
  rfl
theorem sub11060 (p : Pattern) : d2540 (change p 225 (some 224)) = d31 p := by
  change d31 (change p 225 (some 224)) = d31 p
  exact sub11059 p
theorem sub11061 (p : Pattern) : d2569 (change p 225 (some 224)) = d6075 p := by
  change (if p 204 then d2542 (change p 225 (some 224)) else d2540 (change p 225 (some 224))) = d6075 p
  rw [sub11029, sub11060]
  rfl
theorem sub11062 (p : Pattern) : d1742 (change p 225 (some 224)) = d1742 p := by
  change (if p 247 then d4 (change p 225 (some 224)) else d2 (change p 225 (some 224))) = d1742 p
  rw [sub10967, sub10974]
  rfl
theorem sub11063 (p : Pattern) : d1743 (change p 225 (some 224)) = d1743 p := by
  change (if p 246 then d17 (change p 225 (some 224)) else d1742 (change p 225 (some 224))) = d1743 p
  rw [sub10969, sub11062]
  rfl
theorem sub11064 (p : Pattern) : d2570 (change p 225 (some 224)) = d1743 p := by
  change d1743 (change p 225 (some 224)) = d1743 p
  exact sub11063 p
theorem sub11065 (p : Pattern) : d2571 (change p 225 (some 224)) = d1743 p := by
  change d2570 (change p 225 (some 224)) = d1743 p
  exact sub11064 p
theorem sub11066 (p : Pattern) : d2572 (change p 225 (some 224)) = d6076 p := by
  change (if p 204 then d12 (change p 225 (some 224)) else d2571 (change p 225 (some 224))) = d6076 p
  rw [sub10962, sub11065]
  rfl
theorem sub11067 (p : Pattern) : d2573 (change p 225 (some 224)) = d6077 p := by
  change (if p 182 then d2572 (change p 225 (some 224)) else d2569 (change p 225 (some 224))) = d6077 p
  rw [sub11066, sub11061]
  rfl
theorem sub11068 (p : Pattern) : d2574 (change p 225 (some 224)) = d6078 p := by
  change (if p 163 then d2573 (change p 225 (some 224)) else d2568 (change p 225 (some 224))) = d6078 p
  rw [sub11067, sub11058]
  rfl
theorem sub11069 (p : Pattern) : d2575 (change p 225 (some 224)) = d6079 p := by
  change (if p 163 then d2536 (change p 225 (some 224)) else d2527 (change p 225 (some 224))) = d6079 p
  rw [sub11022, sub11004]
  rfl
theorem sub11070 (p : Pattern) : d2576 (change p 225 (some 224)) = d6080 p := by
  change (if p 162 then d2575 (change p 225 (some 224)) else d2574 (change p 225 (some 224))) = d6080 p
  rw [sub11069, sub11068]
  rfl
theorem sub11071 (p : Pattern) : d58 (change p 225 (some 224)) = d58 p := by
  change (if p 246 then d57 (change p 225 (some 224)) else d10 (change p 225 (some 224))) = d58 p
  rw [sub11034, sub11032]
  rfl
theorem sub11072 (p : Pattern) : d2577 (change p 225 (some 224)) = d58 p := by
  change d58 (change p 225 (some 224)) = d58 p
  exact sub11071 p
theorem sub11073 (p : Pattern) : d329 (change p 225 (some 224)) = d329 p := by
  change (if p 246 then d12 (change p 225 (some 224)) else d57 (change p 225 (some 224))) = d329 p
  rw [sub10962, sub11034]
  rfl
theorem sub11074 (p : Pattern) : d330 (change p 225 (some 224)) = d329 p := by
  change d329 (change p 225 (some 224)) = d329 p
  exact sub11073 p
theorem sub11075 (p : Pattern) : d2578 (change p 225 (some 224)) = d329 p := by
  change d330 (change p 225 (some 224)) = d329 p
  exact sub11074 p
theorem sub11076 (p : Pattern) : d2579 (change p 225 (some 224)) = d6081 p := by
  change (if p 204 then d2578 (change p 225 (some 224)) else d2577 (change p 225 (some 224))) = d6081 p
  rw [sub11075, sub11072]
  rfl
theorem sub11077 (p : Pattern) : d2580 (change p 225 (some 224)) = d6082 p := by
  change (if p 204 then d12 (change p 225 (some 224)) else d2578 (change p 225 (some 224))) = d6082 p
  rw [sub10962, sub11075]
  rfl
theorem sub11078 (p : Pattern) : d2581 (change p 225 (some 224)) = d6083 p := by
  change (if p 182 then d2580 (change p 225 (some 224)) else d2579 (change p 225 (some 224))) = d6083 p
  rw [sub11077, sub11076]
  rfl
theorem sub11079 (p : Pattern) : d2582 (change p 225 (some 224)) = d6084 p := by
  change (if p 163 then d2581 (change p 225 (some 224)) else d2527 (change p 225 (some 224))) = d6084 p
  rw [sub11078, sub11004]
  rfl
theorem sub11080 (p : Pattern) : d40 (change p 225 (some 224)) = d40 p := by
  change (if p 246 then d39 (change p 225 (some 224)) else d11 (change p 225 (some 224))) = d40 p
  rw [sub11017, sub11015]
  rfl
theorem sub11081 (p : Pattern) : d2551 (change p 225 (some 224)) = d40 p := by
  change d40 (change p 225 (some 224)) = d40 p
  exact sub11080 p
theorem sub11082 (p : Pattern) : d2583 (change p 225 (some 224)) = d6085 p := by
  change (if p 204 then d2552 (change p 225 (some 224)) else d2551 (change p 225 (some 224))) = d6085 p
  rw [sub11043, sub11081]
  rfl
theorem sub11083 (p : Pattern) : d2584 (change p 225 (some 224)) = d6086 p := by
  change (if p 182 then d2553 (change p 225 (some 224)) else d2583 (change p 225 (some 224))) = d6086 p
  rw [sub11044, sub11082]
  rfl
theorem sub11084 (p : Pattern) : d2585 (change p 225 (some 224)) = d6087 p := by
  change (if p 163 then d12 (change p 225 (some 224)) else d2584 (change p 225 (some 224))) = d6087 p
  rw [sub10962, sub11083]
  rfl
theorem sub11085 (p : Pattern) : d2586 (change p 225 (some 224)) = d6088 p := by
  change (if p 162 then d2585 (change p 225 (some 224)) else d2582 (change p 225 (some 224))) = d6088 p
  rw [sub11084, sub11079]
  rfl
theorem sub11086 (p : Pattern) : d2587 (change p 225 (some 224)) = d6089 p := by
  change (if p 161 then d2586 (change p 225 (some 224)) else d2576 (change p 225 (some 224))) = d6089 p
  rw [sub11085, sub11070]
  rfl
theorem sub11087 (p : Pattern) : d2588 (change p 225 (some 224)) = d6090 p := by
  change (if p 182 then d12 (change p 225 (some 224)) else d2569 (change p 225 (some 224))) = d6090 p
  rw [sub10962, sub11061]
  rfl
theorem sub11088 (p : Pattern) : d2589 (change p 225 (some 224)) = d6091 p := by
  change (if p 163 then d2588 (change p 225 (some 224)) else d2549 (change p 225 (some 224))) = d6091 p
  rw [sub11087, sub11039]
  rfl
theorem sub11089 (p : Pattern) : d2590 (change p 225 (some 224)) = d6092 p := by
  change (if p 163 then d2560 (change p 225 (some 224)) else d2555 (change p 225 (some 224))) = d6092 p
  rw [sub11051, sub11046]
  rfl
theorem sub11090 (p : Pattern) : d2591 (change p 225 (some 224)) = d6093 p := by
  change (if p 162 then d2590 (change p 225 (some 224)) else d2589 (change p 225 (some 224))) = d6093 p
  rw [sub11089, sub11088]
  rfl
theorem sub11091 (p : Pattern) : d2592 (change p 225 (some 224)) = d6094 p := by
  change (if p 182 then d12 (change p 225 (some 224)) else d2579 (change p 225 (some 224))) = d6094 p
  rw [sub10962, sub11076]
  rfl
theorem sub11092 (p : Pattern) : d2593 (change p 225 (some 224)) = d6095 p := by
  change (if p 163 then d2592 (change p 225 (some 224)) else d2555 (change p 225 (some 224))) = d6095 p
  rw [sub11091, sub11046]
  rfl
theorem sub11093 (p : Pattern) : d2594 (change p 225 (some 224)) = d6096 p := by
  change (if p 182 then d12 (change p 225 (some 224)) else d2583 (change p 225 (some 224))) = d6096 p
  rw [sub10962, sub11082]
  rfl
theorem sub11094 (p : Pattern) : d2595 (change p 225 (some 224)) = d6097 p := by
  change (if p 163 then d12 (change p 225 (some 224)) else d2594 (change p 225 (some 224))) = d6097 p
  rw [sub10962, sub11093]
  rfl
theorem sub11095 (p : Pattern) : d2596 (change p 225 (some 224)) = d6098 p := by
  change (if p 162 then d2595 (change p 225 (some 224)) else d2593 (change p 225 (some 224))) = d6098 p
  rw [sub11094, sub11092]
  rfl
theorem sub11096 (p : Pattern) : d2597 (change p 225 (some 224)) = d6099 p := by
  change (if p 161 then d2596 (change p 225 (some 224)) else d2591 (change p 225 (some 224))) = d6099 p
  rw [sub11095, sub11090]
  rfl
theorem sub11097 (p : Pattern) : d2598 (change p 225 (some 224)) = d6100 p := by
  change (if p 160 then d2597 (change p 225 (some 224)) else d2587 (change p 225 (some 224))) = d6100 p
  rw [sub11096, sub11086]
  rfl
theorem sub11098 (p : Pattern) : d2599 (change p 225 (some 224)) = d6101 p := by
  change (if p 141 then d2598 (change p 225 (some 224)) else d2564 (change p 225 (some 224))) = d6101 p
  rw [sub11097, sub11055]
  rfl
theorem sub11099 (p : Pattern) : d2600 (change p 225 (some 224)) = d6102 p := by
  change (if p 204 then d12 (change p 225 (some 224)) else d2507 (change p 225 (some 224))) = d6102 p
  rw [sub10962, sub10972]
  rfl
theorem sub11100 (p : Pattern) : d2601 (change p 225 (some 224)) = d6103 p := by
  change (if p 182 then d2600 (change p 225 (some 224)) else d2518 (change p 225 (some 224))) = d6103 p
  rw [sub11099, sub10986]
  rfl
theorem sub11101 (p : Pattern) : d2602 (change p 225 (some 224)) = d6104 p := by
  change (if p 204 then d12 (change p 225 (some 224)) else d2522 (change p 225 (some 224))) = d6104 p
  rw [sub10962, sub10995]
  rfl
theorem sub11102 (p : Pattern) : d2603 (change p 225 (some 224)) = d6105 p := by
  change (if p 182 then d2602 (change p 225 (some 224)) else d2523 (change p 225 (some 224))) = d6105 p
  rw [sub11101, sub10996]
  rfl
theorem sub11103 (p : Pattern) : d2604 (change p 225 (some 224)) = d6106 p := by
  change (if p 163 then d2603 (change p 225 (some 224)) else d2601 (change p 225 (some 224))) = d6106 p
  rw [sub11102, sub11100]
  rfl
theorem sub11104 (p : Pattern) : d2605 (change p 225 (some 224)) = d6107 p := by
  change (if p 162 then d2604 (change p 225 (some 224)) else d2601 (change p 225 (some 224))) = d6107 p
  rw [sub11103, sub11100]
  rfl
theorem sub11105 (p : Pattern) : d2606 (change p 225 (some 224)) = d6108 p := by
  change (if p 204 then d12 (change p 225 (some 224)) else d2531 (change p 225 (some 224))) = d6108 p
  rw [sub10962, sub11013]
  rfl
theorem sub11106 (p : Pattern) : d2607 (change p 225 (some 224)) = d6109 p := by
  change (if p 182 then d2606 (change p 225 (some 224)) else d2532 (change p 225 (some 224))) = d6109 p
  rw [sub11105, sub11014]
  rfl
theorem sub11107 (p : Pattern) : d2608 (change p 225 (some 224)) = d6110 p := by
  change (if p 163 then d12 (change p 225 (some 224)) else d2607 (change p 225 (some 224))) = d6110 p
  rw [sub10962, sub11106]
  rfl
theorem sub11108 (p : Pattern) : d2609 (change p 225 (some 224)) = d6111 p := by
  change (if p 162 then d2608 (change p 225 (some 224)) else d2604 (change p 225 (some 224))) = d6111 p
  rw [sub11107, sub11103]
  rfl
theorem sub11109 (p : Pattern) : d2610 (change p 225 (some 224)) = d6112 p := by
  change (if p 161 then d2609 (change p 225 (some 224)) else d2605 (change p 225 (some 224))) = d6112 p
  rw [sub11108, sub11104]
  rfl
theorem sub11110 (p : Pattern) : d2611 (change p 225 (some 224)) = d6113 p := by
  change (if p 182 then d2543 (change p 225 (some 224)) else d2569 (change p 225 (some 224))) = d6113 p
  rw [sub11030, sub11061]
  rfl
theorem sub11111 (p : Pattern) : d35 (change p 225 (some 224)) = d35 p := by
  change (if p 246 then d34 (change p 225 (some 224)) else d6 (change p 225 (some 224))) = d35 p
  rw [sub10999, sub10997]
  rfl
theorem sub11112 (p : Pattern) : d2545 (change p 225 (some 224)) = d35 p := by
  change d35 (change p 225 (some 224)) = d35 p
  exact sub11111 p
theorem sub11113 (p : Pattern) : d2612 (change p 225 (some 224)) = d6114 p := by
  change (if p 204 then d2547 (change p 225 (some 224)) else d2545 (change p 225 (some 224))) = d6114 p
  rw [sub11037, sub11112]
  rfl
theorem sub11114 (p : Pattern) : d2613 (change p 225 (some 224)) = d6115 p := by
  change (if p 182 then d2548 (change p 225 (some 224)) else d2612 (change p 225 (some 224))) = d6115 p
  rw [sub11038, sub11113]
  rfl
theorem sub11115 (p : Pattern) : d2614 (change p 225 (some 224)) = d6116 p := by
  change (if p 163 then d2613 (change p 225 (some 224)) else d2611 (change p 225 (some 224))) = d6116 p
  rw [sub11114, sub11110]
  rfl
theorem sub11116 (p : Pattern) : d2615 (change p 225 (some 224)) = d6117 p := by
  change (if p 162 then d2585 (change p 225 (some 224)) else d2614 (change p 225 (some 224))) = d6117 p
  rw [sub11084, sub11115]
  rfl
theorem sub11117 (p : Pattern) : d2616 (change p 225 (some 224)) = d6118 p := by
  change (if p 161 then d12 (change p 225 (some 224)) else d2615 (change p 225 (some 224))) = d6118 p
  rw [sub10962, sub11116]
  rfl
theorem sub11118 (p : Pattern) : d2617 (change p 225 (some 224)) = d6119 p := by
  change (if p 160 then d2616 (change p 225 (some 224)) else d2610 (change p 225 (some 224))) = d6119 p
  rw [sub11117, sub11109]
  rfl
theorem sub11119 (p : Pattern) : d2618 (change p 225 (some 224)) = d6120 p := by
  change (if p 163 then d2611 (change p 225 (some 224)) else d2601 (change p 225 (some 224))) = d6120 p
  rw [sub11110, sub11100]
  rfl
theorem sub11120 (p : Pattern) : d2619 (change p 225 (some 224)) = d6121 p := by
  change (if p 163 then d2607 (change p 225 (some 224)) else d2603 (change p 225 (some 224))) = d6121 p
  rw [sub11106, sub11102]
  rfl
theorem sub11121 (p : Pattern) : d2620 (change p 225 (some 224)) = d6122 p := by
  change (if p 162 then d2619 (change p 225 (some 224)) else d2618 (change p 225 (some 224))) = d6122 p
  rw [sub11120, sub11119]
  rfl
theorem sub11122 (p : Pattern) : d2621 (change p 225 (some 224)) = d6123 p := by
  change (if p 163 then d2581 (change p 225 (some 224)) else d2603 (change p 225 (some 224))) = d6123 p
  rw [sub11078, sub11102]
  rfl
theorem sub11123 (p : Pattern) : d2622 (change p 225 (some 224)) = d6124 p := by
  change (if p 162 then d2585 (change p 225 (some 224)) else d2621 (change p 225 (some 224))) = d6124 p
  rw [sub11084, sub11122]
  rfl
theorem sub11124 (p : Pattern) : d2623 (change p 225 (some 224)) = d6125 p := by
  change (if p 161 then d2622 (change p 225 (some 224)) else d2620 (change p 225 (some 224))) = d6125 p
  rw [sub11123, sub11121]
  rfl
theorem sub11125 (p : Pattern) : d2624 (change p 225 (some 224)) = d6126 p := by
  change (if p 163 then d12 (change p 225 (some 224)) else d2613 (change p 225 (some 224))) = d6126 p
  rw [sub10962, sub11114]
  rfl
theorem sub11126 (p : Pattern) : d2625 (change p 225 (some 224)) = d6127 p := by
  change (if p 162 then d12 (change p 225 (some 224)) else d2624 (change p 225 (some 224))) = d6127 p
  rw [sub10962, sub11125]
  rfl
theorem sub11127 (p : Pattern) : d2626 (change p 225 (some 224)) = d6128 p := by
  change (if p 161 then d12 (change p 225 (some 224)) else d2625 (change p 225 (some 224))) = d6128 p
  rw [sub10962, sub11126]
  rfl
theorem sub11128 (p : Pattern) : d2627 (change p 225 (some 224)) = d6129 p := by
  change (if p 160 then d2626 (change p 225 (some 224)) else d2623 (change p 225 (some 224))) = d6129 p
  rw [sub11127, sub11124]
  rfl
theorem sub11129 (p : Pattern) : d2628 (change p 225 (some 224)) = d6130 p := by
  change (if p 141 then d2627 (change p 225 (some 224)) else d2617 (change p 225 (some 224))) = d6130 p
  rw [sub11128, sub11118]
  rfl
theorem sub11130 (p : Pattern) : d2629 (change p 225 (some 224)) = d6131 p := by
  change (if p 138 then d2628 (change p 225 (some 224)) else d2599 (change p 225 (some 224))) = d6131 p
  rw [sub11129, sub11098]
  rfl
theorem sub11131 (p : Pattern) : d2630 (change p 225 (some 224)) = d6132 p := by
  change (if p 163 then d2584 (change p 225 (some 224)) else d2607 (change p 225 (some 224))) = d6132 p
  rw [sub11083, sub11106]
  rfl
theorem sub11132 (p : Pattern) : d2631 (change p 225 (some 224)) = d6133 p := by
  change (if p 162 then d2585 (change p 225 (some 224)) else d2630 (change p 225 (some 224))) = d6133 p
  rw [sub11084, sub11131]
  rfl
theorem sub11133 (p : Pattern) : d2632 (change p 225 (some 224)) = d6134 p := by
  change (if p 162 then d12 (change p 225 (some 224)) else d2585 (change p 225 (some 224))) = d6134 p
  rw [sub10962, sub11084]
  rfl
theorem sub11134 (p : Pattern) : d2633 (change p 225 (some 224)) = d6135 p := by
  change (if p 161 then d2632 (change p 225 (some 224)) else d2631 (change p 225 (some 224))) = d6135 p
  rw [sub11133, sub11132]
  rfl
theorem sub11135 (p : Pattern) : d2634 (change p 225 (some 224)) = d6136 p := by
  change (if p 161 then d12 (change p 225 (some 224)) else d2632 (change p 225 (some 224))) = d6136 p
  rw [sub10962, sub11133]
  rfl
theorem sub11136 (p : Pattern) : d2635 (change p 225 (some 224)) = d6137 p := by
  change (if p 160 then d2634 (change p 225 (some 224)) else d2633 (change p 225 (some 224))) = d6137 p
  rw [sub11135, sub11134]
  rfl
theorem sub11137 (p : Pattern) : d2636 (change p 225 (some 224)) = d6138 p := by
  change (if p 160 then d12 (change p 225 (some 224)) else d2634 (change p 225 (some 224))) = d6138 p
  rw [sub10962, sub11135]
  rfl
theorem sub11138 (p : Pattern) : d2637 (change p 225 (some 224)) = d6139 p := by
  change (if p 141 then d2636 (change p 225 (some 224)) else d2635 (change p 225 (some 224))) = d6139 p
  rw [sub11137, sub11136]
  rfl
theorem sub11139 (p : Pattern) : d2638 (change p 225 (some 224)) = d6140 p := by
  change (if p 138 then d2637 (change p 225 (some 224)) else d2628 (change p 225 (some 224))) = d6140 p
  rw [sub11138, sub11129]
  rfl
theorem sub11140 (p : Pattern) : d2639 (change p 225 (some 224)) = d6141 p := by
  change (if p 116 then d2638 (change p 225 (some 224)) else d2629 (change p 225 (some 224))) = d6141 p
  rw [sub11139, sub11130]
  rfl
theorem sub11141 (p : Pattern) : d2640 (change p 225 (some 224)) = d6046 p := by
  change (if p 163 then d2519 (change p 225 (some 224)) else d2516 (change p 225 (some 224))) = d6046 p
  rw [sub10987, sub10984]
  simp only [ite_self]
theorem sub11142 (p : Pattern) : d2641 (change p 225 (some 224)) = d6051 p := by
  change (if p 162 then d2528 (change p 225 (some 224)) else d2640 (change p 225 (some 224))) = d6051 p
  rw [sub11005, sub11141]
  rfl
theorem sub11143 (p : Pattern) : d2642 (change p 225 (some 224)) = d6057 p := by
  change (if p 161 then d2538 (change p 225 (some 224)) else d2641 (change p 225 (some 224))) = d6057 p
  rw [sub11024, sub11142]
  rfl
theorem sub11144 (p : Pattern) : d2643 (change p 225 (some 224)) = d6074 p := by
  change (if p 160 then d2563 (change p 225 (some 224)) else d2642 (change p 225 (some 224))) = d6074 p
  rw [sub11054, sub11143]
  rfl
theorem sub11145 (p : Pattern) : d2644 (change p 225 (some 224)) = d6078 p := by
  change (if p 163 then d2573 (change p 225 (some 224)) else d2519 (change p 225 (some 224))) = d6078 p
  rw [sub11067, sub10987]
  rfl
theorem sub11146 (p : Pattern) : d2645 (change p 225 (some 224)) = d6080 p := by
  change (if p 162 then d2575 (change p 225 (some 224)) else d2644 (change p 225 (some 224))) = d6080 p
  rw [sub11069, sub11145]
  rfl
theorem sub11147 (p : Pattern) : d2646 (change p 225 (some 224)) = d6089 p := by
  change (if p 161 then d2586 (change p 225 (some 224)) else d2645 (change p 225 (some 224))) = d6089 p
  rw [sub11085, sub11146]
  rfl
theorem sub11148 (p : Pattern) : d2647 (change p 225 (some 224)) = d6100 p := by
  change (if p 160 then d2597 (change p 225 (some 224)) else d2646 (change p 225 (some 224))) = d6100 p
  rw [sub11096, sub11147]
  rfl
theorem sub11149 (p : Pattern) : d2648 (change p 225 (some 224)) = d6101 p := by
  change (if p 141 then d2647 (change p 225 (some 224)) else d2643 (change p 225 (some 224))) = d6101 p
  rw [sub11148, sub11144]
  rfl
theorem sub11150 (p : Pattern) : d2649 (change p 225 (some 224)) = d6131 p := by
  change (if p 138 then d2628 (change p 225 (some 224)) else d2648 (change p 225 (some 224))) = d6131 p
  rw [sub11129, sub11149]
  rfl
theorem sub11151 (p : Pattern) : d2650 (change p 225 (some 224)) = d6142 p := by
  change (if p 138 then d12 (change p 225 (some 224)) else d2628 (change p 225 (some 224))) = d6142 p
  rw [sub10962, sub11129]
  rfl
theorem sub11152 (p : Pattern) : d2651 (change p 225 (some 224)) = d6143 p := by
  change (if p 116 then d2650 (change p 225 (some 224)) else d2649 (change p 225 (some 224))) = d6143 p
  rw [sub11151, sub11150]
  rfl
theorem sub11153 (p : Pattern) : d2652 (change p 225 (some 224)) = d6144 p := by
  change (if p 115 then d2651 (change p 225 (some 224)) else d2639 (change p 225 (some 224))) = d6144 p
  rw [sub11152, sub11140]
  rfl
theorem sub11154 (p : Pattern) : d2654 (change p 225 (some 224)) = d14 p := by
  change d2504 (change p 225 (some 224)) = d14 p
  exact sub10965 p
theorem sub11155 (p : Pattern) : d2655 (change p 225 (some 224)) = d6044 p := by
  change (if p 204 then d2507 (change p 225 (some 224)) else d2654 (change p 225 (some 224))) = d6044 p
  rw [sub10972, sub11154]
  rfl
theorem sub11156 (p : Pattern) : d2656 (change p 225 (some 224)) = d6046 p := by
  change (if p 182 then d2511 (change p 225 (some 224)) else d2655 (change p 225 (some 224))) = d6046 p
  rw [sub10980, sub11155]
  rfl
theorem sub11157 (p : Pattern) : d2657 (change p 225 (some 224)) = d6046 p := by
  change (if p 163 then d2519 (change p 225 (some 224)) else d2656 (change p 225 (some 224))) = d6046 p
  rw [sub10987, sub11156]
  simp only [ite_self]
theorem sub11158 (p : Pattern) : d2658 (change p 225 (some 224)) = d6051 p := by
  change (if p 162 then d2528 (change p 225 (some 224)) else d2657 (change p 225 (some 224))) = d6051 p
  rw [sub11005, sub11157]
  rfl
theorem sub11159 (p : Pattern) : d2659 (change p 225 (some 224)) = d6057 p := by
  change (if p 161 then d2538 (change p 225 (some 224)) else d2658 (change p 225 (some 224))) = d6057 p
  rw [sub11024, sub11158]
  rfl
end NetHack.Sokoban22Refined85
