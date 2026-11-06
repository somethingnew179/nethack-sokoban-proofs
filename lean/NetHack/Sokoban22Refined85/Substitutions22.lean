/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions21
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2640 (p : Pattern) : d276 (change p 10000 (some 71)) = d276 p := by
  change (if p 162 then d275 (change p 10000 (some 71)) else d271 (change p 10000 (some 71))) = d276 p
  rw [sub2639, sub2635]
  rfl
theorem sub2641 (p : Pattern) : d277 (change p 10000 (some 71)) = d277 p := by
  change (if p 182 then d12 (change p 10000 (some 71)) else d59 (change p 10000 (some 71))) = d277 p
  rw [sub1531, sub1584]
  rfl
theorem sub2642 (p : Pattern) : d278 (change p 10000 (some 71)) = d278 p := by
  change (if p 163 then d12 (change p 10000 (some 71)) else d277 (change p 10000 (some 71))) = d278 p
  rw [sub1531, sub2641]
  rfl
theorem sub2643 (p : Pattern) : d279 (change p 10000 (some 71)) = d279 p := by
  change (if p 162 then d278 (change p 10000 (some 71)) else d275 (change p 10000 (some 71))) = d279 p
  rw [sub2642, sub2639]
  rfl
theorem sub2644 (p : Pattern) : d280 (change p 10000 (some 71)) = d280 p := by
  change (if p 161 then d279 (change p 10000 (some 71)) else d276 (change p 10000 (some 71))) = d280 p
  rw [sub2643, sub2640]
  rfl
theorem sub2645 (p : Pattern) : d281 (change p 10000 (some 71)) = d281 p := by
  change (if p 160 then d280 (change p 10000 (some 71)) else d114 (change p 10000 (some 71))) = d281 p
  rw [sub2644, sub1641]
  rfl
theorem sub2646 (p : Pattern) : d282 (change p 10000 (some 71)) = d282 p := by
  change (if p 204 then d107 (change p 10000 (some 71)) else d116 (change p 10000 (some 71))) = d282 p
  rw [sub1634, sub1644]
  rfl
theorem sub2647 (p : Pattern) : d283 (change p 10000 (some 71)) = d283 p := by
  change (if p 182 then d12 (change p 10000 (some 71)) else d282 (change p 10000 (some 71))) = d283 p
  rw [sub1531, sub2646]
  rfl
theorem sub2648 (p : Pattern) : d284 (change p 10000 (some 71)) = d284 p := by
  change (if p 163 then d283 (change p 10000 (some 71)) else d270 (change p 10000 (some 71))) = d284 p
  rw [sub2647, sub2634]
  rfl
theorem sub2649 (p : Pattern) : d285 (change p 10000 (some 71)) = d285 p := by
  change (if p 163 then d12 (change p 10000 (some 71)) else d274 (change p 10000 (some 71))) = d285 p
  rw [sub1531, sub2638]
  rfl
theorem sub2650 (p : Pattern) : d286 (change p 10000 (some 71)) = d286 p := by
  change (if p 162 then d285 (change p 10000 (some 71)) else d284 (change p 10000 (some 71))) = d286 p
  rw [sub2649, sub2648]
  rfl
theorem sub2651 (p : Pattern) : d287 (change p 10000 (some 71)) = d287 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d285 (change p 10000 (some 71))) = d287 p
  rw [sub1531, sub2649]
  rfl
theorem sub2652 (p : Pattern) : d288 (change p 10000 (some 71)) = d288 p := by
  change (if p 161 then d287 (change p 10000 (some 71)) else d286 (change p 10000 (some 71))) = d288 p
  rw [sub2651, sub2650]
  rfl
theorem sub2653 (p : Pattern) : d289 (change p 10000 (some 71)) = d289 p := by
  change (if p 160 then d288 (change p 10000 (some 71)) else d214 (change p 10000 (some 71))) = d289 p
  rw [sub2652, sub1744]
  rfl
theorem sub2654 (p : Pattern) : d290 (change p 10000 (some 71)) = d290 p := by
  change (if p 141 then d289 (change p 10000 (some 71)) else d281 (change p 10000 (some 71))) = d290 p
  rw [sub2653, sub2645]
  rfl
theorem sub2655 (p : Pattern) : d291 (change p 10000 (some 71)) = d291 p := by
  change (if p 163 then d269 (change p 10000 (some 71)) else d105 (change p 10000 (some 71))) = d291 p
  rw [sub2633, sub1631]
  rfl
theorem sub2656 (p : Pattern) : d292 (change p 10000 (some 71)) = d292 p := by
  change (if p 182 then d121 (change p 10000 (some 71)) else d273 (change p 10000 (some 71))) = d292 p
  rw [sub1650, sub2637]
  rfl
theorem sub2657 (p : Pattern) : d293 (change p 10000 (some 71)) = d293 p := by
  change (if p 163 then d292 (change p 10000 (some 71)) else d269 (change p 10000 (some 71))) = d293 p
  rw [sub2656, sub2633]
  rfl
theorem sub2658 (p : Pattern) : d294 (change p 10000 (some 71)) = d294 p := by
  change (if p 162 then d293 (change p 10000 (some 71)) else d291 (change p 10000 (some 71))) = d294 p
  rw [sub2657, sub2655]
  rfl
theorem sub2659 (p : Pattern) : d295 (change p 10000 (some 71)) = d295 p := by
  change (if p 162 then d278 (change p 10000 (some 71)) else d293 (change p 10000 (some 71))) = d295 p
  rw [sub2642, sub2657]
  rfl
theorem sub2660 (p : Pattern) : d296 (change p 10000 (some 71)) = d296 p := by
  change (if p 161 then d295 (change p 10000 (some 71)) else d294 (change p 10000 (some 71))) = d296 p
  rw [sub2659, sub2658]
  rfl
theorem sub2661 (p : Pattern) : d297 (change p 10000 (some 71)) = d297 p := by
  change (if p 160 then d151 (change p 10000 (some 71)) else d296 (change p 10000 (some 71))) = d297 p
  rw [sub1680, sub2660]
  rfl
theorem sub2662 (p : Pattern) : d298 (change p 10000 (some 71)) = d298 p := by
  change (if p 182 then d108 (change p 10000 (some 71)) else d282 (change p 10000 (some 71))) = d298 p
  rw [sub1635, sub2646]
  rfl
theorem sub2663 (p : Pattern) : d299 (change p 10000 (some 71)) = d299 p := by
  change (if p 163 then d298 (change p 10000 (some 71)) else d269 (change p 10000 (some 71))) = d299 p
  rw [sub2662, sub2633]
  rfl
theorem sub2664 (p : Pattern) : d300 (change p 10000 (some 71)) = d300 p := by
  change (if p 163 then d12 (change p 10000 (some 71)) else d292 (change p 10000 (some 71))) = d300 p
  rw [sub1531, sub2656]
  rfl
theorem sub2665 (p : Pattern) : d301 (change p 10000 (some 71)) = d301 p := by
  change (if p 162 then d300 (change p 10000 (some 71)) else d299 (change p 10000 (some 71))) = d301 p
  rw [sub2664, sub2663]
  rfl
theorem sub2666 (p : Pattern) : d302 (change p 10000 (some 71)) = d302 p := by
  change (if p 162 then d12 (change p 10000 (some 71)) else d300 (change p 10000 (some 71))) = d302 p
  rw [sub1531, sub2664]
  rfl
theorem sub2667 (p : Pattern) : d303 (change p 10000 (some 71)) = d303 p := by
  change (if p 161 then d302 (change p 10000 (some 71)) else d301 (change p 10000 (some 71))) = d303 p
  rw [sub2666, sub2665]
  rfl
theorem sub2668 (p : Pattern) : d304 (change p 10000 (some 71)) = d304 p := by
  change (if p 160 then d155 (change p 10000 (some 71)) else d303 (change p 10000 (some 71))) = d304 p
  rw [sub1684, sub2667]
  rfl
theorem sub2669 (p : Pattern) : d305 (change p 10000 (some 71)) = d305 p := by
  change (if p 141 then d304 (change p 10000 (some 71)) else d297 (change p 10000 (some 71))) = d305 p
  rw [sub2668, sub2661]
  rfl
theorem sub2670 (p : Pattern) : d306 (change p 10000 (some 71)) = d306 p := by
  change (if p 138 then d305 (change p 10000 (some 71)) else d290 (change p 10000 (some 71))) = d306 p
  rw [sub2669, sub2654]
  rfl
theorem sub2671 (p : Pattern) : d307 (change p 10000 (some 71)) = d307 p := by
  change (if p 138 then d12 (change p 10000 (some 71)) else d305 (change p 10000 (some 71))) = d307 p
  rw [sub1531, sub2669]
  rfl
theorem sub2672 (p : Pattern) : d308 (change p 10000 (some 71)) = d308 p := by
  change (if p 116 then d307 (change p 10000 (some 71)) else d306 (change p 10000 (some 71))) = d308 p
  rw [sub2671, sub2670]
  rfl
theorem sub2673 (p : Pattern) : d309 (change p 10000 (some 71)) = d309 p := by
  change (if p 115 then d308 (change p 10000 (some 71)) else d225 (change p 10000 (some 71))) = d309 p
  rw [sub2672, sub1755]
  rfl
theorem sub2674 (p : Pattern) : d310 (change p 10000 (some 71)) = d309 p := by
  change d309 (change p 10000 (some 71)) = d309 p
  exact sub2673 p
theorem sub2675 (p : Pattern) : d311 (change p 10000 (some 71)) = d4109 p := by
  change (if p 49 then d310 (change p 10000 (some 71)) else d101 (change p 10000 (some 71))) = d4109 p
  rw [sub2674, sub1626]
  rfl
theorem sub2676 (p : Pattern) : d312 (change p 10000 (some 71)) = d4110 p := by
  change (if p 48 then d311 (change p 10000 (some 71)) else d169 (change p 10000 (some 71))) = d4110 p
  rw [sub2675, sub1698]
  rfl
theorem sub2677 (p : Pattern) : d0 (change p 138 (some 160)) = d0 p := by
  rfl
theorem sub2678 (p : Pattern) : d12 (change p 138 (some 160)) = d12 p := by
  rfl
theorem sub2679 (p : Pattern) : d13 (change p 138 (some 160)) = d13 p := by
  change (if p 247 then d12 (change p 138 (some 160)) else d0 (change p 138 (some 160))) = d13 p
  rw [sub2678, sub2677]
  rfl
theorem sub2680 (p : Pattern) : d14 (change p 138 (some 160)) = d14 p := by
  change (if p 246 then d13 (change p 138 (some 160)) else d0 (change p 138 (some 160))) = d14 p
  rw [sub2679, sub2677]
  rfl
theorem sub2681 (p : Pattern) : d2 (change p 138 (some 160)) = d2 p := by
  rfl
theorem sub2682 (p : Pattern) : d30 (change p 138 (some 160)) = d30 p := by
  change (if p 247 then d12 (change p 138 (some 160)) else d2 (change p 138 (some 160))) = d30 p
  rw [sub2678, sub2681]
  rfl
theorem sub2683 (p : Pattern) : d31 (change p 138 (some 160)) = d31 p := by
  change (if p 246 then d30 (change p 138 (some 160)) else d2 (change p 138 (some 160))) = d31 p
  rw [sub2682, sub2681]
  rfl
theorem sub2684 (p : Pattern) : d32 (change p 138 (some 160)) = d32 p := by
  change (if p 204 then d12 (change p 138 (some 160)) else d31 (change p 138 (some 160))) = d32 p
  rw [sub2678, sub2683]
  rfl
theorem sub2685 (p : Pattern) : d33 (change p 138 (some 160)) = d33 p := by
  change (if p 182 then d32 (change p 138 (some 160)) else d14 (change p 138 (some 160))) = d33 p
  rw [sub2684, sub2680]
  rfl
theorem sub2686 (p : Pattern) : d6 (change p 138 (some 160)) = d6 p := by
  rfl
theorem sub2687 (p : Pattern) : d34 (change p 138 (some 160)) = d34 p := by
  change (if p 247 then d12 (change p 138 (some 160)) else d6 (change p 138 (some 160))) = d34 p
  rw [sub2678, sub2686]
  rfl
theorem sub2688 (p : Pattern) : d35 (change p 138 (some 160)) = d35 p := by
  change (if p 246 then d34 (change p 138 (some 160)) else d6 (change p 138 (some 160))) = d35 p
  rw [sub2687, sub2686]
  rfl
theorem sub2689 (p : Pattern) : d36 (change p 138 (some 160)) = d36 p := by
  change (if p 204 then d12 (change p 138 (some 160)) else d35 (change p 138 (some 160))) = d36 p
  rw [sub2678, sub2688]
  rfl
theorem sub2690 (p : Pattern) : d37 (change p 138 (some 160)) = d37 p := by
  change (if p 182 then d36 (change p 138 (some 160)) else d14 (change p 138 (some 160))) = d37 p
  rw [sub2689, sub2680]
  rfl
theorem sub2691 (p : Pattern) : d38 (change p 138 (some 160)) = d38 p := by
  change (if p 163 then d37 (change p 138 (some 160)) else d33 (change p 138 (some 160))) = d38 p
  rw [sub2690, sub2685]
  rfl
theorem sub2692 (p : Pattern) : d11 (change p 138 (some 160)) = d11 p := by
  rfl
theorem sub2693 (p : Pattern) : d39 (change p 138 (some 160)) = d39 p := by
  change (if p 247 then d12 (change p 138 (some 160)) else d11 (change p 138 (some 160))) = d39 p
  rw [sub2678, sub2692]
  rfl
theorem sub2694 (p : Pattern) : d40 (change p 138 (some 160)) = d40 p := by
  change (if p 246 then d39 (change p 138 (some 160)) else d11 (change p 138 (some 160))) = d40 p
  rw [sub2693, sub2692]
  rfl
theorem sub2695 (p : Pattern) : d41 (change p 138 (some 160)) = d41 p := by
  change (if p 204 then d12 (change p 138 (some 160)) else d40 (change p 138 (some 160))) = d41 p
  rw [sub2678, sub2694]
  rfl
theorem sub2696 (p : Pattern) : d42 (change p 138 (some 160)) = d42 p := by
  change (if p 182 then d41 (change p 138 (some 160)) else d14 (change p 138 (some 160))) = d42 p
  rw [sub2695, sub2680]
  rfl
theorem sub2697 (p : Pattern) : d4 (change p 138 (some 160)) = d4 p := by
  rfl
theorem sub2698 (p : Pattern) : d17 (change p 138 (some 160)) = d17 p := by
  change (if p 247 then d12 (change p 138 (some 160)) else d4 (change p 138 (some 160))) = d17 p
  rw [sub2678, sub2697]
  rfl
theorem sub2699 (p : Pattern) : d18 (change p 138 (some 160)) = d18 p := by
  change (if p 246 then d17 (change p 138 (some 160)) else d4 (change p 138 (some 160))) = d18 p
  rw [sub2698, sub2697]
  rfl
theorem sub2700 (p : Pattern) : d43 (change p 138 (some 160)) = d43 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d18 (change p 138 (some 160))) = d43 p
  rw [sub2678, sub2699]
  rfl
theorem sub2701 (p : Pattern) : d44 (change p 138 (some 160)) = d44 p := by
  change (if p 163 then d43 (change p 138 (some 160)) else d42 (change p 138 (some 160))) = d44 p
  rw [sub2700, sub2696]
  rfl
theorem sub2702 (p : Pattern) : d45 (change p 138 (some 160)) = d45 p := by
  change (if p 162 then d44 (change p 138 (some 160)) else d38 (change p 138 (some 160))) = d45 p
  rw [sub2701, sub2691]
  rfl
theorem sub2703 (p : Pattern) : d46 (change p 138 (some 160)) = d46 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d14 (change p 138 (some 160))) = d46 p
  rw [sub2678, sub2680]
  rfl
theorem sub2704 (p : Pattern) : d47 (change p 138 (some 160)) = d47 p := by
  change (if p 163 then d43 (change p 138 (some 160)) else d46 (change p 138 (some 160))) = d47 p
  rw [sub2700, sub2703]
  rfl
theorem sub2705 (p : Pattern) : d9 (change p 138 (some 160)) = d9 p := by
  rfl
theorem sub2706 (p : Pattern) : d23 (change p 138 (some 160)) = d23 p := by
  change (if p 247 then d12 (change p 138 (some 160)) else d9 (change p 138 (some 160))) = d23 p
  rw [sub2678, sub2705]
  rfl
theorem sub2707 (p : Pattern) : d24 (change p 138 (some 160)) = d24 p := by
  change (if p 246 then d23 (change p 138 (some 160)) else d9 (change p 138 (some 160))) = d24 p
  rw [sub2706, sub2705]
  rfl
theorem sub2708 (p : Pattern) : d48 (change p 138 (some 160)) = d48 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d24 (change p 138 (some 160))) = d48 p
  rw [sub2678, sub2707]
  rfl
theorem sub2709 (p : Pattern) : d49 (change p 138 (some 160)) = d49 p := by
  change (if p 163 then d12 (change p 138 (some 160)) else d48 (change p 138 (some 160))) = d49 p
  rw [sub2678, sub2708]
  rfl
theorem sub2710 (p : Pattern) : d50 (change p 138 (some 160)) = d50 p := by
  change (if p 162 then d49 (change p 138 (some 160)) else d47 (change p 138 (some 160))) = d50 p
  rw [sub2709, sub2704]
  rfl
theorem sub2711 (p : Pattern) : d51 (change p 138 (some 160)) = d51 p := by
  change (if p 161 then d50 (change p 138 (some 160)) else d45 (change p 138 (some 160))) = d51 p
  rw [sub2710, sub2702]
  rfl
theorem sub2712 (p : Pattern) : d52 (change p 138 (some 160)) = d51 p := by
  change d51 (change p 138 (some 160)) = d51 p
  exact sub2711 p
theorem sub2713 (p : Pattern) : d66 (change p 138 (some 160)) = d66 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d31 (change p 138 (some 160))) = d66 p
  rw [sub2678, sub2683]
  rfl
theorem sub2714 (p : Pattern) : d67 (change p 138 (some 160)) = d67 p := by
  change (if p 163 then d66 (change p 138 (some 160)) else d37 (change p 138 (some 160))) = d67 p
  rw [sub2713, sub2690]
  rfl
theorem sub2715 (p : Pattern) : d68 (change p 138 (some 160)) = d68 p := by
  change (if p 163 then d48 (change p 138 (some 160)) else d43 (change p 138 (some 160))) = d68 p
  rw [sub2708, sub2700]
  rfl
theorem sub2716 (p : Pattern) : d69 (change p 138 (some 160)) = d69 p := by
  change (if p 162 then d68 (change p 138 (some 160)) else d67 (change p 138 (some 160))) = d69 p
  rw [sub2715, sub2714]
  rfl
theorem sub2717 (p : Pattern) : d10 (change p 138 (some 160)) = d10 p := by
  rfl
theorem sub2718 (p : Pattern) : d57 (change p 138 (some 160)) = d57 p := by
  change (if p 247 then d12 (change p 138 (some 160)) else d10 (change p 138 (some 160))) = d57 p
  rw [sub2678, sub2717]
  rfl
theorem sub2719 (p : Pattern) : d58 (change p 138 (some 160)) = d58 p := by
  change (if p 246 then d57 (change p 138 (some 160)) else d10 (change p 138 (some 160))) = d58 p
  rw [sub2718, sub2717]
  rfl
theorem sub2720 (p : Pattern) : d70 (change p 138 (some 160)) = d70 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d58 (change p 138 (some 160))) = d70 p
  rw [sub2678, sub2719]
  rfl
theorem sub2721 (p : Pattern) : d71 (change p 138 (some 160)) = d71 p := by
  change (if p 163 then d70 (change p 138 (some 160)) else d43 (change p 138 (some 160))) = d71 p
  rw [sub2720, sub2700]
  rfl
theorem sub2722 (p : Pattern) : d72 (change p 138 (some 160)) = d72 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d40 (change p 138 (some 160))) = d72 p
  rw [sub2678, sub2694]
  rfl
theorem sub2723 (p : Pattern) : d73 (change p 138 (some 160)) = d73 p := by
  change (if p 163 then d12 (change p 138 (some 160)) else d72 (change p 138 (some 160))) = d73 p
  rw [sub2678, sub2722]
  rfl
theorem sub2724 (p : Pattern) : d74 (change p 138 (some 160)) = d74 p := by
  change (if p 162 then d73 (change p 138 (some 160)) else d71 (change p 138 (some 160))) = d74 p
  rw [sub2723, sub2721]
  rfl
theorem sub2725 (p : Pattern) : d75 (change p 138 (some 160)) = d75 p := by
  change (if p 161 then d74 (change p 138 (some 160)) else d69 (change p 138 (some 160))) = d75 p
  rw [sub2724, sub2716]
  rfl
theorem sub2726 (p : Pattern) : d76 (change p 138 (some 160)) = d75 p := by
  change d75 (change p 138 (some 160)) = d75 p
  exact sub2725 p
theorem sub2727 (p : Pattern) : d77 (change p 138 (some 160)) = d4120 p := by
  change (if p 141 then d76 (change p 138 (some 160)) else d52 (change p 138 (some 160))) = d4120 p
  rw [sub2726, sub2712]
  rfl
theorem sub2728 (p : Pattern) : d517 (change p 138 (some 160)) = d4120 p := by
  change d77 (change p 138 (some 160)) = d4120 p
  exact sub2727 p
theorem sub2729 (p : Pattern) : d518 (change p 138 (some 160)) = d518 p := by
  change (if p 204 then d18 (change p 138 (some 160)) else d14 (change p 138 (some 160))) = d518 p
  rw [sub2699, sub2680]
  rfl
theorem sub2730 (p : Pattern) : d519 (change p 138 (some 160)) = d519 p := by
  change (if p 182 then d36 (change p 138 (some 160)) else d518 (change p 138 (some 160))) = d519 p
  rw [sub2689, sub2729]
  rfl
theorem sub2731 (p : Pattern) : d59 (change p 138 (some 160)) = d59 p := by
  change (if p 204 then d12 (change p 138 (some 160)) else d58 (change p 138 (some 160))) = d59 p
  rw [sub2678, sub2719]
  rfl
theorem sub2732 (p : Pattern) : d520 (change p 138 (some 160)) = d520 p := by
  change (if p 182 then d59 (change p 138 (some 160)) else d518 (change p 138 (some 160))) = d520 p
  rw [sub2731, sub2729]
  rfl
theorem sub2733 (p : Pattern) : d521 (change p 138 (some 160)) = d521 p := by
  change (if p 163 then d520 (change p 138 (some 160)) else d519 (change p 138 (some 160))) = d521 p
  rw [sub2732, sub2730]
  rfl
theorem sub2734 (p : Pattern) : d522 (change p 138 (some 160)) = d522 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d518 (change p 138 (some 160))) = d522 p
  rw [sub2678, sub2729]
  rfl
theorem sub2735 (p : Pattern) : d8 (change p 138 (some 160)) = d8 p := by
  rfl
theorem sub2736 (p : Pattern) : d190 (change p 138 (some 160)) = d190 p := by
  change (if p 247 then d12 (change p 138 (some 160)) else d8 (change p 138 (some 160))) = d190 p
  rw [sub2678, sub2735]
  rfl
theorem sub2737 (p : Pattern) : d191 (change p 138 (some 160)) = d191 p := by
  change (if p 246 then d190 (change p 138 (some 160)) else d8 (change p 138 (some 160))) = d191 p
  rw [sub2736, sub2735]
  rfl
theorem sub2738 (p : Pattern) : d523 (change p 138 (some 160)) = d523 p := by
  change (if p 204 then d191 (change p 138 (some 160)) else d18 (change p 138 (some 160))) = d523 p
  rw [sub2737, sub2699]
  rfl
theorem sub2739 (p : Pattern) : d524 (change p 138 (some 160)) = d524 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d523 (change p 138 (some 160))) = d524 p
  rw [sub2678, sub2738]
  rfl
theorem sub2740 (p : Pattern) : d525 (change p 138 (some 160)) = d525 p := by
  change (if p 163 then d524 (change p 138 (some 160)) else d522 (change p 138 (some 160))) = d525 p
  rw [sub2739, sub2734]
  rfl
theorem sub2741 (p : Pattern) : d526 (change p 138 (some 160)) = d526 p := by
  change (if p 162 then d525 (change p 138 (some 160)) else d521 (change p 138 (some 160))) = d526 p
  rw [sub2740, sub2733]
  rfl
theorem sub2742 (p : Pattern) : d25 (change p 138 (some 160)) = d25 p := by
  change (if p 204 then d12 (change p 138 (some 160)) else d24 (change p 138 (some 160))) = d25 p
  rw [sub2678, sub2707]
  rfl
theorem sub2743 (p : Pattern) : d527 (change p 138 (some 160)) = d527 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d25 (change p 138 (some 160))) = d527 p
  rw [sub2678, sub2742]
  rfl
theorem sub2744 (p : Pattern) : d528 (change p 138 (some 160)) = d528 p := by
  change (if p 163 then d12 (change p 138 (some 160)) else d527 (change p 138 (some 160))) = d528 p
  rw [sub2678, sub2743]
  rfl
theorem sub2745 (p : Pattern) : d529 (change p 138 (some 160)) = d529 p := by
  change (if p 162 then d528 (change p 138 (some 160)) else d525 (change p 138 (some 160))) = d529 p
  rw [sub2744, sub2740]
  rfl
theorem sub2746 (p : Pattern) : d530 (change p 138 (some 160)) = d530 p := by
  change (if p 161 then d529 (change p 138 (some 160)) else d526 (change p 138 (some 160))) = d530 p
  rw [sub2745, sub2741]
  rfl
theorem sub2747 (p : Pattern) : d531 (change p 138 (some 160)) = d530 p := by
  change d530 (change p 138 (some 160)) = d530 p
  exact sub2746 p
theorem sub2748 (p : Pattern) : d532 (change p 138 (some 160)) = d532 p := by
  change (if p 204 then d35 (change p 138 (some 160)) else d31 (change p 138 (some 160))) = d532 p
  rw [sub2688, sub2683]
  rfl
theorem sub2749 (p : Pattern) : d533 (change p 138 (some 160)) = d533 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d532 (change p 138 (some 160))) = d533 p
  rw [sub2678, sub2748]
  rfl
theorem sub2750 (p : Pattern) : d534 (change p 138 (some 160)) = d534 p := by
  change (if p 163 then d533 (change p 138 (some 160)) else d520 (change p 138 (some 160))) = d534 p
  rw [sub2749, sub2732]
  rfl
theorem sub2751 (p : Pattern) : d535 (change p 138 (some 160)) = d535 p := by
  change (if p 163 then d527 (change p 138 (some 160)) else d524 (change p 138 (some 160))) = d535 p
  rw [sub2743, sub2739]
  rfl
theorem sub2752 (p : Pattern) : d536 (change p 138 (some 160)) = d536 p := by
  change (if p 162 then d535 (change p 138 (some 160)) else d534 (change p 138 (some 160))) = d536 p
  rw [sub2751, sub2750]
  rfl
theorem sub2753 (p : Pattern) : d277 (change p 138 (some 160)) = d277 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d59 (change p 138 (some 160))) = d277 p
  rw [sub2678, sub2731]
  rfl
theorem sub2754 (p : Pattern) : d537 (change p 138 (some 160)) = d537 p := by
  change (if p 163 then d277 (change p 138 (some 160)) else d524 (change p 138 (some 160))) = d537 p
  rw [sub2753, sub2739]
  rfl
theorem sub2755 (p : Pattern) : d538 (change p 138 (some 160)) = d538 p := by
  change (if p 182 then d12 (change p 138 (some 160)) else d41 (change p 138 (some 160))) = d538 p
  rw [sub2678, sub2695]
  rfl
theorem sub2756 (p : Pattern) : d539 (change p 138 (some 160)) = d539 p := by
  change (if p 163 then d12 (change p 138 (some 160)) else d538 (change p 138 (some 160))) = d539 p
  rw [sub2678, sub2755]
  rfl
theorem sub2757 (p : Pattern) : d540 (change p 138 (some 160)) = d540 p := by
  change (if p 162 then d539 (change p 138 (some 160)) else d537 (change p 138 (some 160))) = d540 p
  rw [sub2756, sub2754]
  rfl
theorem sub2758 (p : Pattern) : d541 (change p 138 (some 160)) = d541 p := by
  change (if p 161 then d540 (change p 138 (some 160)) else d536 (change p 138 (some 160))) = d541 p
  rw [sub2757, sub2752]
  rfl
theorem sub2759 (p : Pattern) : d542 (change p 138 (some 160)) = d541 p := by
  change d541 (change p 138 (some 160)) = d541 p
  exact sub2758 p
end NetHack.Sokoban22Refined85
