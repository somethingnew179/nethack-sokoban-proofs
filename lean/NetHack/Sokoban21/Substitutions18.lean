/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions17
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s2700 (pattern : Twelve) : d1667 (change pattern 8 7) = d22 pattern := by
  change d183 (change pattern 8 7) = d22 pattern
  exact s2699 pattern
theorem s2701 (pattern : Twelve) : d1718 (change pattern 8 7) = d2348 pattern := by
  change (if pattern.f then d1667 (change pattern 8 7) else d42 (change pattern 8 7)) = d2348 pattern
  rw [s2700, s2570]
  rfl
theorem s2702 (pattern : Twelve) : d1252 (change pattern 8 7) = d6 pattern := by
  change d6 (change pattern 8 7) = d6 pattern
  exact s2577 pattern
theorem s2703 (pattern : Twelve) : d1626 (change pattern 8 7) = d6 pattern := by
  change (if pattern.f then d6 (change pattern 8 7) else d1252 (change pattern 8 7)) = d6 pattern
  rw [s2577, s2702]
  simp only [ite_self]
theorem s2704 (pattern : Twelve) : d1721 (change pattern 8 7) = d2349 pattern := by
  change (if pattern.e then d1626 (change pattern 8 7) else d1718 (change pattern 8 7)) = d2349 pattern
  rw [s2703, s2701]
  rfl
theorem s2705 (pattern : Twelve) : d1724 (change pattern 8 7) = d2350 pattern := by
  change (if pattern.j then d1721 (change pattern 8 7) else d1719 (change pattern 8 7)) = d2350 pattern
  rw [s2704, s2690]
  rfl
theorem s2706 (pattern : Twelve) : d1726 (change pattern 8 7) = d2351 pattern := by
  change (if pattern.d then d1723 (change pattern 8 7) else d1724 (change pattern 8 7)) = d2351 pattern
  rw [s2695, s2705]
  rfl
theorem s2707 (pattern : Twelve) : d1728 (change pattern 8 7) = d2352 pattern := by
  change (if pattern.c then d1726 (change pattern 8 7) else d1719 (change pattern 8 7)) = d2352 pattern
  rw [s2706, s2690]
  rfl
theorem s2708 (pattern : Twelve) : d1729 (change pattern 8 7) = d2353 pattern := by
  change (if pattern.a then d1728 (change pattern 8 7) else d1727 (change pattern 8 7)) = d2353 pattern
  rw [s2707, s2697]
  rfl
theorem s2709 (pattern : Twelve) : d0 (change pattern 8 5) = d0 pattern := by
  rfl
theorem s2710 (pattern : Twelve) : d171 (change pattern 8 5) = d0 pattern := by
  change d0 (change pattern 8 5) = d0 pattern
  exact s2709 pattern
theorem s2711 (pattern : Twelve) : d1 (change pattern 8 5) = d1 pattern := by
  rfl
theorem s2712 (pattern : Twelve) : d7 (change pattern 8 5) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 8 5) else d0 (change pattern 8 5)) = d7 pattern
  rw [s2711, s2709]
  rfl
theorem s2713 (pattern : Twelve) : d17 (change pattern 8 5) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 8 5) else d0 (change pattern 8 5)) = d17 pattern
  rw [s2712, s2709]
  rfl
theorem s2714 (pattern : Twelve) : d366 (change pattern 8 5) = d17 pattern := by
  change d17 (change pattern 8 5) = d17 pattern
  exact s2713 pattern
theorem s2715 (pattern : Twelve) : d372 (change pattern 8 5) = d2357 pattern := by
  change (if pattern.h then d366 (change pattern 8 5) else d171 (change pattern 8 5)) = d2357 pattern
  rw [s2714, s2710]
  rfl
theorem s2716 (pattern : Twelve) : d389 (change pattern 8 5) = d2357 pattern := by
  change d372 (change pattern 8 5) = d2357 pattern
  exact s2715 pattern
theorem s2717 (pattern : Twelve) : d2 (change pattern 8 5) = d2 pattern := by
  rfl
theorem s2718 (pattern : Twelve) : d10 (change pattern 8 5) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 8 5) else d0 (change pattern 8 5)) = d10 pattern
  rw [s2717, s2709]
  rfl
theorem s2719 (pattern : Twelve) : d3 (change pattern 8 5) = d3 pattern := by
  rfl
theorem s2720 (pattern : Twelve) : d11 (change pattern 8 5) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 8 5) else d1 (change pattern 8 5)) = d11 pattern
  rw [s2719, s2711]
  rfl
theorem s2721 (pattern : Twelve) : d19 (change pattern 8 5) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 8 5) else d10 (change pattern 8 5)) = d19 pattern
  rw [s2720, s2718]
  rfl
theorem s2722 (pattern : Twelve) : d29 (change pattern 8 5) = d19 pattern := by
  change d19 (change pattern 8 5) = d19 pattern
  exact s2721 pattern
theorem s2723 (pattern : Twelve) : d374 (change pattern 8 5) = d2358 pattern := by
  change (if pattern.h then d29 (change pattern 8 5) else d366 (change pattern 8 5)) = d2358 pattern
  rw [s2722, s2714]
  rfl
theorem s2724 (pattern : Twelve) : d390 (change pattern 8 5) = d2358 pattern := by
  change d374 (change pattern 8 5) = d2358 pattern
  exact s2723 pattern
theorem s2725 (pattern : Twelve) : d402 (change pattern 8 5) = d2359 pattern := by
  change (if pattern.e then d390 (change pattern 8 5) else d389 (change pattern 8 5)) = d2359 pattern
  rw [s2724, s2716]
  rfl
theorem s2726 (pattern : Twelve) : d369 (change pattern 8 5) = d0 pattern := by
  change d0 (change pattern 8 5) = d0 pattern
  exact s2709 pattern
theorem s2727 (pattern : Twelve) : d36 (change pattern 8 5) = d17 pattern := by
  change d17 (change pattern 8 5) = d17 pattern
  exact s2713 pattern
theorem s2728 (pattern : Twelve) : d376 (change pattern 8 5) = d2357 pattern := by
  change (if pattern.h then d36 (change pattern 8 5) else d369 (change pattern 8 5)) = d2357 pattern
  rw [s2727, s2726]
  rfl
theorem s2729 (pattern : Twelve) : d391 (change pattern 8 5) = d2357 pattern := by
  change d376 (change pattern 8 5) = d2357 pattern
  exact s2728 pattern
theorem s2730 (pattern : Twelve) : d378 (change pattern 8 5) = d2358 pattern := by
  change (if pattern.h then d29 (change pattern 8 5) else d36 (change pattern 8 5)) = d2358 pattern
  rw [s2722, s2727]
  rfl
theorem s2731 (pattern : Twelve) : d392 (change pattern 8 5) = d2358 pattern := by
  change d378 (change pattern 8 5) = d2358 pattern
  exact s2730 pattern
theorem s2732 (pattern : Twelve) : d403 (change pattern 8 5) = d2359 pattern := by
  change (if pattern.e then d392 (change pattern 8 5) else d391 (change pattern 8 5)) = d2359 pattern
  rw [s2731, s2729]
  rfl
theorem s2733 (pattern : Twelve) : d409 (change pattern 8 5) = d2359 pattern := by
  change (if pattern.j then d403 (change pattern 8 5) else d402 (change pattern 8 5)) = d2359 pattern
  rw [s2732, s2725]
  simp only [ite_self]
theorem s2734 (pattern : Twelve) : d35 (change pattern 8 5) = d0 pattern := by
  change d0 (change pattern 8 5) = d0 pattern
  exact s2709 pattern
theorem s2735 (pattern : Twelve) : d380 (change pattern 8 5) = d2357 pattern := by
  change (if pattern.h then d36 (change pattern 8 5) else d35 (change pattern 8 5)) = d2357 pattern
  rw [s2727, s2734]
  rfl
theorem s2736 (pattern : Twelve) : d393 (change pattern 8 5) = d2357 pattern := by
  change d380 (change pattern 8 5) = d2357 pattern
  exact s2735 pattern
theorem s2737 (pattern : Twelve) : d394 (change pattern 8 5) = d2358 pattern := by
  change d378 (change pattern 8 5) = d2358 pattern
  exact s2730 pattern
theorem s2738 (pattern : Twelve) : d404 (change pattern 8 5) = d2359 pattern := by
  change (if pattern.e then d394 (change pattern 8 5) else d393 (change pattern 8 5)) = d2359 pattern
  rw [s2737, s2736]
  rfl
theorem s2739 (pattern : Twelve) : d410 (change pattern 8 5) = d2359 pattern := by
  change (if pattern.j then d404 (change pattern 8 5) else d403 (change pattern 8 5)) = d2359 pattern
  rw [s2738, s2732]
  simp only [ite_self]
theorem s2740 (pattern : Twelve) : d415 (change pattern 8 5) = d2359 pattern := by
  change (if pattern.d then d410 (change pattern 8 5) else d409 (change pattern 8 5)) = d2359 pattern
  rw [s2739, s2733]
  simp only [ite_self]
theorem s2741 (pattern : Twelve) : d371 (change pattern 8 5) = d0 pattern := by
  change d0 (change pattern 8 5) = d0 pattern
  exact s2709 pattern
theorem s2742 (pattern : Twelve) : d382 (change pattern 8 5) = d2357 pattern := by
  change (if pattern.h then d36 (change pattern 8 5) else d371 (change pattern 8 5)) = d2357 pattern
  rw [s2727, s2741]
  rfl
theorem s2743 (pattern : Twelve) : d395 (change pattern 8 5) = d2357 pattern := by
  change d382 (change pattern 8 5) = d2357 pattern
  exact s2742 pattern
theorem s2744 (pattern : Twelve) : d396 (change pattern 8 5) = d2358 pattern := by
  change d378 (change pattern 8 5) = d2358 pattern
  exact s2730 pattern
theorem s2745 (pattern : Twelve) : d405 (change pattern 8 5) = d2359 pattern := by
  change (if pattern.e then d396 (change pattern 8 5) else d395 (change pattern 8 5)) = d2359 pattern
  rw [s2744, s2743]
  rfl
theorem s2746 (pattern : Twelve) : d39 (change pattern 8 5) = d2 pattern := by
  change d2 (change pattern 8 5) = d2 pattern
  exact s2717 pattern
theorem s2747 (pattern : Twelve) : d9 (change pattern 8 5) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 8 5) else d2 (change pattern 8 5)) = d9 pattern
  rw [s2719, s2717]
  rfl
theorem s2748 (pattern : Twelve) : d23 (change pattern 8 5) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 8 5) else d2 (change pattern 8 5)) = d23 pattern
  rw [s2747, s2717]
  rfl
theorem s2749 (pattern : Twelve) : d40 (change pattern 8 5) = d23 pattern := by
  change d23 (change pattern 8 5) = d23 pattern
  exact s2748 pattern
theorem s2750 (pattern : Twelve) : d384 (change pattern 8 5) = d2360 pattern := by
  change (if pattern.h then d40 (change pattern 8 5) else d39 (change pattern 8 5)) = d2360 pattern
  rw [s2749, s2746]
  rfl
theorem s2751 (pattern : Twelve) : d397 (change pattern 8 5) = d2360 pattern := by
  change d384 (change pattern 8 5) = d2360 pattern
  exact s2750 pattern
theorem s2752 (pattern : Twelve) : d4 (change pattern 8 5) = d4 pattern := by
  rfl
theorem s2753 (pattern : Twelve) : d16 (change pattern 8 5) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 8 5) else d2 (change pattern 8 5)) = d16 pattern
  rw [s2752, s2717]
  rfl
theorem s2754 (pattern : Twelve) : d5 (change pattern 8 5) = d5 pattern := by
  rfl
theorem s2755 (pattern : Twelve) : d12 (change pattern 8 5) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 8 5) else d3 (change pattern 8 5)) = d12 pattern
  rw [s2754, s2719]
  rfl
theorem s2756 (pattern : Twelve) : d25 (change pattern 8 5) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 8 5) else d16 (change pattern 8 5)) = d25 pattern
  rw [s2755, s2753]
  rfl
theorem s2757 (pattern : Twelve) : d42 (change pattern 8 5) = d25 pattern := by
  change d25 (change pattern 8 5) = d25 pattern
  exact s2756 pattern
theorem s2758 (pattern : Twelve) : d385 (change pattern 8 5) = d2361 pattern := by
  change (if pattern.h then d42 (change pattern 8 5) else d40 (change pattern 8 5)) = d2361 pattern
  rw [s2757, s2749]
  rfl
theorem s2759 (pattern : Twelve) : d398 (change pattern 8 5) = d2361 pattern := by
  change d385 (change pattern 8 5) = d2361 pattern
  exact s2758 pattern
theorem s2760 (pattern : Twelve) : d406 (change pattern 8 5) = d2362 pattern := by
  change (if pattern.e then d398 (change pattern 8 5) else d397 (change pattern 8 5)) = d2362 pattern
  rw [s2759, s2751]
  rfl
theorem s2761 (pattern : Twelve) : d411 (change pattern 8 5) = d2363 pattern := by
  change (if pattern.j then d406 (change pattern 8 5) else d405 (change pattern 8 5)) = d2363 pattern
  rw [s2760, s2745]
  rfl
theorem s2762 (pattern : Twelve) : d399 (change pattern 8 5) = d2357 pattern := by
  change d380 (change pattern 8 5) = d2357 pattern
  exact s2735 pattern
theorem s2763 (pattern : Twelve) : d407 (change pattern 8 5) = d2359 pattern := by
  change (if pattern.e then d394 (change pattern 8 5) else d399 (change pattern 8 5)) = d2359 pattern
  rw [s2737, s2762]
  rfl
theorem s2764 (pattern : Twelve) : d6 (change pattern 8 5) = d6 pattern := by
  rfl
theorem s2765 (pattern : Twelve) : d412 (change pattern 8 5) = d2364 pattern := by
  change (if pattern.j then d6 (change pattern 8 5) else d407 (change pattern 8 5)) = d2364 pattern
  rw [s2764, s2763]
  rfl
theorem s2766 (pattern : Twelve) : d416 (change pattern 8 5) = d2365 pattern := by
  change (if pattern.d then d412 (change pattern 8 5) else d411 (change pattern 8 5)) = d2365 pattern
  rw [s2765, s2761]
  rfl
theorem s2767 (pattern : Twelve) : d419 (change pattern 8 5) = d2366 pattern := by
  change (if pattern.c then d416 (change pattern 8 5) else d415 (change pattern 8 5)) = d2366 pattern
  rw [s2766, s2740]
  rfl
theorem s2768 (pattern : Twelve) : d413 (change pattern 8 5) = d2363 pattern := by
  change (if pattern.j then d406 (change pattern 8 5) else d407 (change pattern 8 5)) = d2363 pattern
  rw [s2760, s2763]
  rfl
theorem s2769 (pattern : Twelve) : d417 (change pattern 8 5) = d2365 pattern := by
  change (if pattern.d then d412 (change pattern 8 5) else d413 (change pattern 8 5)) = d2365 pattern
  rw [s2765, s2768]
  rfl
theorem s2770 (pattern : Twelve) : d420 (change pattern 8 5) = d2366 pattern := by
  change (if pattern.c then d417 (change pattern 8 5) else d407 (change pattern 8 5)) = d2366 pattern
  rw [s2769, s2763]
  rfl
theorem s2771 (pattern : Twelve) : d422 (change pattern 8 5) = d2366 pattern := by
  change (if pattern.g then d420 (change pattern 8 5) else d419 (change pattern 8 5)) = d2366 pattern
  rw [s2770, s2767]
  simp only [ite_self]
theorem s2772 (pattern : Twelve) : d423 (change pattern 8 5) = d2366 pattern := by
  change (if pattern.b then d420 (change pattern 8 5) else d422 (change pattern 8 5)) = d2366 pattern
  rw [s2770, s2771]
  simp only [ite_self]
theorem s2773 (pattern : Twelve) : d117 (change pattern 8 5) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 8 5) else d3 (change pattern 8 5)) = d117 pattern
  rw [s2752, s2719]
  rfl
theorem s2774 (pattern : Twelve) : d119 (change pattern 8 5) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 8 5) else d3 (change pattern 8 5)) = d119 pattern
  rw [s2773, s2719]
  rfl
theorem s2775 (pattern : Twelve) : d125 (change pattern 8 5) = d119 pattern := by
  change d119 (change pattern 8 5) = d119 pattern
  exact s2774 pattern
theorem s2776 (pattern : Twelve) : d386 (change pattern 8 5) = d2367 pattern := by
  change (if pattern.h then d125 (change pattern 8 5) else d39 (change pattern 8 5)) = d2367 pattern
  rw [s2775, s2746]
  rfl
theorem s2777 (pattern : Twelve) : d400 (change pattern 8 5) = d2367 pattern := by
  change d386 (change pattern 8 5) = d2367 pattern
  exact s2776 pattern
theorem s2778 (pattern : Twelve) : d13 (change pattern 8 5) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 8 5) else d4 (change pattern 8 5)) = d13 pattern
  rw [s2764, s2752]
  rfl
theorem s2779 (pattern : Twelve) : d20 (change pattern 8 5) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 8 5) else d12 (change pattern 8 5)) = d20 pattern
  rw [s2778, s2755]
  rfl
theorem s2780 (pattern : Twelve) : d128 (change pattern 8 5) = d20 pattern := by
  change d20 (change pattern 8 5) = d20 pattern
  exact s2779 pattern
theorem s2781 (pattern : Twelve) : d388 (change pattern 8 5) = d2368 pattern := by
  change (if pattern.h then d128 (change pattern 8 5) else d40 (change pattern 8 5)) = d2368 pattern
  rw [s2780, s2749]
  rfl
theorem s2782 (pattern : Twelve) : d401 (change pattern 8 5) = d2368 pattern := by
  change d388 (change pattern 8 5) = d2368 pattern
  exact s2781 pattern
theorem s2783 (pattern : Twelve) : d408 (change pattern 8 5) = d2369 pattern := by
  change (if pattern.e then d401 (change pattern 8 5) else d400 (change pattern 8 5)) = d2369 pattern
  rw [s2782, s2777]
  rfl
theorem s2784 (pattern : Twelve) : d414 (change pattern 8 5) = d2370 pattern := by
  change (if pattern.j then d408 (change pattern 8 5) else d407 (change pattern 8 5)) = d2370 pattern
  rw [s2783, s2763]
  rfl
theorem s2785 (pattern : Twelve) : d418 (change pattern 8 5) = d2371 pattern := by
  change (if pattern.d then d412 (change pattern 8 5) else d414 (change pattern 8 5)) = d2371 pattern
  rw [s2765, s2784]
  rfl
theorem s2786 (pattern : Twelve) : d421 (change pattern 8 5) = d2372 pattern := by
  change (if pattern.c then d418 (change pattern 8 5) else d407 (change pattern 8 5)) = d2372 pattern
  rw [s2785, s2763]
  rfl
theorem s2787 (pattern : Twelve) : d424 (change pattern 8 5) = d2373 pattern := by
  change (if pattern.a then d421 (change pattern 8 5) else d423 (change pattern 8 5)) = d2373 pattern
  rw [s2786, s2772]
  rfl
theorem s2788 (pattern : Twelve) : d814 (change pattern 8 5) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 8 5) else d7 (change pattern 8 5)) = d814 pattern
  rw [s2711, s2712]
  rfl
theorem s2789 (pattern : Twelve) : d818 (change pattern 8 5) = d814 pattern := by
  change d814 (change pattern 8 5) = d814 pattern
  exact s2788 pattern
theorem s2790 (pattern : Twelve) : d1030 (change pattern 8 5) = d2374 pattern := by
  change (if pattern.h then d818 (change pattern 8 5) else d366 (change pattern 8 5)) = d2374 pattern
  rw [s2789, s2714]
  rfl
theorem s2791 (pattern : Twelve) : d1038 (change pattern 8 5) = d2374 pattern := by
  change d1030 (change pattern 8 5) = d2374 pattern
  exact s2790 pattern
theorem s2792 (pattern : Twelve) : d1032 (change pattern 8 5) = d2375 pattern := by
  change (if pattern.h then d42 (change pattern 8 5) else d29 (change pattern 8 5)) = d2375 pattern
  rw [s2757, s2722]
  rfl
theorem s2793 (pattern : Twelve) : d1039 (change pattern 8 5) = d2375 pattern := by
  change d1032 (change pattern 8 5) = d2375 pattern
  exact s2792 pattern
theorem s2794 (pattern : Twelve) : d1048 (change pattern 8 5) = d2376 pattern := by
  change (if pattern.e then d1039 (change pattern 8 5) else d1038 (change pattern 8 5)) = d2376 pattern
  rw [s2793, s2791]
  rfl
theorem s2795 (pattern : Twelve) : d1033 (change pattern 8 5) = d2374 pattern := by
  change (if pattern.h then d818 (change pattern 8 5) else d36 (change pattern 8 5)) = d2374 pattern
  rw [s2789, s2727]
  rfl
theorem s2796 (pattern : Twelve) : d1040 (change pattern 8 5) = d2374 pattern := by
  change d1033 (change pattern 8 5) = d2374 pattern
  exact s2795 pattern
theorem s2797 (pattern : Twelve) : d1041 (change pattern 8 5) = d2375 pattern := by
  change d1032 (change pattern 8 5) = d2375 pattern
  exact s2792 pattern
theorem s2798 (pattern : Twelve) : d1049 (change pattern 8 5) = d2376 pattern := by
  change (if pattern.e then d1041 (change pattern 8 5) else d1040 (change pattern 8 5)) = d2376 pattern
  rw [s2797, s2796]
  rfl
theorem s2799 (pattern : Twelve) : d1054 (change pattern 8 5) = d2376 pattern := by
  change (if pattern.j then d1049 (change pattern 8 5) else d1048 (change pattern 8 5)) = d2376 pattern
  rw [s2798, s2794]
  simp only [ite_self]
theorem s2800 (pattern : Twelve) : d1042 (change pattern 8 5) = d2374 pattern := by
  change d1033 (change pattern 8 5) = d2374 pattern
  exact s2795 pattern
theorem s2801 (pattern : Twelve) : d1050 (change pattern 8 5) = d2376 pattern := by
  change (if pattern.e then d1041 (change pattern 8 5) else d1042 (change pattern 8 5)) = d2376 pattern
  rw [s2797, s2800]
  rfl
theorem s2802 (pattern : Twelve) : d1055 (change pattern 8 5) = d2376 pattern := by
  change (if pattern.j then d1050 (change pattern 8 5) else d1049 (change pattern 8 5)) = d2376 pattern
  rw [s2801, s2798]
  simp only [ite_self]
theorem s2803 (pattern : Twelve) : d1060 (change pattern 8 5) = d2376 pattern := by
  change (if pattern.d then d1055 (change pattern 8 5) else d1054 (change pattern 8 5)) = d2376 pattern
  rw [s2802, s2799]
  simp only [ite_self]
theorem s2804 (pattern : Twelve) : d1043 (change pattern 8 5) = d2374 pattern := by
  change d1033 (change pattern 8 5) = d2374 pattern
  exact s2795 pattern
theorem s2805 (pattern : Twelve) : d1051 (change pattern 8 5) = d2376 pattern := by
  change (if pattern.e then d1041 (change pattern 8 5) else d1043 (change pattern 8 5)) = d2376 pattern
  rw [s2797, s2804]
  rfl
theorem s2806 (pattern : Twelve) : d815 (change pattern 8 5) = d815 pattern := by
  change (if pattern.k then d3 (change pattern 8 5) else d9 (change pattern 8 5)) = d815 pattern
  rw [s2719, s2747]
  rfl
theorem s2807 (pattern : Twelve) : d820 (change pattern 8 5) = d815 pattern := by
  change d815 (change pattern 8 5) = d815 pattern
  exact s2806 pattern
theorem s2808 (pattern : Twelve) : d1034 (change pattern 8 5) = d2377 pattern := by
  change (if pattern.h then d820 (change pattern 8 5) else d40 (change pattern 8 5)) = d2377 pattern
  rw [s2807, s2749]
  rfl
theorem s2809 (pattern : Twelve) : d1044 (change pattern 8 5) = d2377 pattern := by
  change d1034 (change pattern 8 5) = d2377 pattern
  exact s2808 pattern
theorem s2810 (pattern : Twelve) : d14 (change pattern 8 5) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 8 5) else d5 (change pattern 8 5)) = d14 pattern
  rw [s2764, s2754]
  rfl
theorem s2811 (pattern : Twelve) : d21 (change pattern 8 5) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 8 5) else d13 (change pattern 8 5)) = d21 pattern
  rw [s2810, s2778]
  rfl
theorem s2812 (pattern : Twelve) : d822 (change pattern 8 5) = d21 pattern := by
  change d21 (change pattern 8 5) = d21 pattern
  exact s2811 pattern
theorem s2813 (pattern : Twelve) : d1035 (change pattern 8 5) = d2378 pattern := by
  change (if pattern.h then d822 (change pattern 8 5) else d42 (change pattern 8 5)) = d2378 pattern
  rw [s2812, s2757]
  rfl
theorem s2814 (pattern : Twelve) : d1045 (change pattern 8 5) = d2378 pattern := by
  change d1035 (change pattern 8 5) = d2378 pattern
  exact s2813 pattern
theorem s2815 (pattern : Twelve) : d1052 (change pattern 8 5) = d2379 pattern := by
  change (if pattern.e then d1045 (change pattern 8 5) else d1044 (change pattern 8 5)) = d2379 pattern
  rw [s2814, s2809]
  rfl
theorem s2816 (pattern : Twelve) : d1056 (change pattern 8 5) = d2380 pattern := by
  change (if pattern.j then d1052 (change pattern 8 5) else d1051 (change pattern 8 5)) = d2380 pattern
  rw [s2815, s2805]
  rfl
theorem s2817 (pattern : Twelve) : d1057 (change pattern 8 5) = d2381 pattern := by
  change (if pattern.j then d6 (change pattern 8 5) else d1050 (change pattern 8 5)) = d2381 pattern
  rw [s2764, s2801]
  rfl
theorem s2818 (pattern : Twelve) : d1061 (change pattern 8 5) = d2382 pattern := by
  change (if pattern.d then d1057 (change pattern 8 5) else d1056 (change pattern 8 5)) = d2382 pattern
  rw [s2817, s2816]
  rfl
theorem s2819 (pattern : Twelve) : d1064 (change pattern 8 5) = d2383 pattern := by
  change (if pattern.c then d1061 (change pattern 8 5) else d1060 (change pattern 8 5)) = d2383 pattern
  rw [s2818, s2803]
  rfl
theorem s2820 (pattern : Twelve) : d1058 (change pattern 8 5) = d2380 pattern := by
  change (if pattern.j then d1052 (change pattern 8 5) else d1050 (change pattern 8 5)) = d2380 pattern
  rw [s2815, s2801]
  rfl
theorem s2821 (pattern : Twelve) : d1062 (change pattern 8 5) = d2382 pattern := by
  change (if pattern.d then d1057 (change pattern 8 5) else d1058 (change pattern 8 5)) = d2382 pattern
  rw [s2817, s2820]
  rfl
theorem s2822 (pattern : Twelve) : d1065 (change pattern 8 5) = d2383 pattern := by
  change (if pattern.c then d1062 (change pattern 8 5) else d1050 (change pattern 8 5)) = d2383 pattern
  rw [s2821, s2801]
  rfl
theorem s2823 (pattern : Twelve) : d1067 (change pattern 8 5) = d2383 pattern := by
  change (if pattern.g then d1065 (change pattern 8 5) else d1064 (change pattern 8 5)) = d2383 pattern
  rw [s2822, s2819]
  simp only [ite_self]
theorem s2824 (pattern : Twelve) : d1068 (change pattern 8 5) = d2383 pattern := by
  change (if pattern.b then d1065 (change pattern 8 5) else d1067 (change pattern 8 5)) = d2383 pattern
  rw [s2822, s2823]
  simp only [ite_self]
theorem s2825 (pattern : Twelve) : d15 (change pattern 8 5) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 8 5) else d4 (change pattern 8 5)) = d15 pattern
  rw [s2754, s2752]
  rfl
theorem s2826 (pattern : Twelve) : d873 (change pattern 8 5) = d873 pattern := by
  change (if pattern.k then d15 (change pattern 8 5) else d117 (change pattern 8 5)) = d873 pattern
  rw [s2825, s2773]
  rfl
theorem s2827 (pattern : Twelve) : d880 (change pattern 8 5) = d873 pattern := by
  change d873 (change pattern 8 5) = d873 pattern
  exact s2826 pattern
theorem s2828 (pattern : Twelve) : d1036 (change pattern 8 5) = d2384 pattern := by
  change (if pattern.h then d880 (change pattern 8 5) else d40 (change pattern 8 5)) = d2384 pattern
  rw [s2827, s2749]
  rfl
theorem s2829 (pattern : Twelve) : d1046 (change pattern 8 5) = d2384 pattern := by
  change d1036 (change pattern 8 5) = d2384 pattern
  exact s2828 pattern
theorem s2830 (pattern : Twelve) : d889 (change pattern 8 5) = d1690 pattern := by
  change (if pattern.h then d6 (change pattern 8 5) else d42 (change pattern 8 5)) = d1690 pattern
  rw [s2764, s2757]
  rfl
theorem s2831 (pattern : Twelve) : d1047 (change pattern 8 5) = d1690 pattern := by
  change d889 (change pattern 8 5) = d1690 pattern
  exact s2830 pattern
theorem s2832 (pattern : Twelve) : d1053 (change pattern 8 5) = d2385 pattern := by
  change (if pattern.e then d1047 (change pattern 8 5) else d1046 (change pattern 8 5)) = d2385 pattern
  rw [s2831, s2829]
  rfl
theorem s2833 (pattern : Twelve) : d1059 (change pattern 8 5) = d2386 pattern := by
  change (if pattern.j then d1053 (change pattern 8 5) else d1050 (change pattern 8 5)) = d2386 pattern
  rw [s2832, s2801]
  rfl
theorem s2834 (pattern : Twelve) : d1063 (change pattern 8 5) = d2387 pattern := by
  change (if pattern.d then d1057 (change pattern 8 5) else d1059 (change pattern 8 5)) = d2387 pattern
  rw [s2817, s2833]
  rfl
theorem s2835 (pattern : Twelve) : d1066 (change pattern 8 5) = d2388 pattern := by
  change (if pattern.c then d1063 (change pattern 8 5) else d1050 (change pattern 8 5)) = d2388 pattern
  rw [s2834, s2801]
  rfl
theorem s2836 (pattern : Twelve) : d1069 (change pattern 8 5) = d2389 pattern := by
  change (if pattern.a then d1066 (change pattern 8 5) else d1068 (change pattern 8 5)) = d2389 pattern
  rw [s2835, s2824]
  rfl
theorem s2837 (pattern : Twelve) : d8 (change pattern 8 5) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 8 5) else d1 (change pattern 8 5)) = d8 pattern
  rw [s2717, s2711]
  rfl
theorem s2838 (pattern : Twelve) : d1275 (change pattern 8 5) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 8 5) else d7 (change pattern 8 5)) = d1275 pattern
  rw [s2837, s2712]
  rfl
theorem s2839 (pattern : Twelve) : d1444 (change pattern 8 5) = d1275 pattern := by
  change d1275 (change pattern 8 5) = d1275 pattern
  exact s2838 pattern
theorem s2840 (pattern : Twelve) : d872 (change pattern 8 5) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 8 5) else d1 (change pattern 8 5)) = d872 pattern
  rw [s2837, s2711]
  rfl
theorem s2841 (pattern : Twelve) : d1280 (change pattern 8 5) = d872 pattern := by
  change d872 (change pattern 8 5) = d872 pattern
  exact s2840 pattern
theorem s2842 (pattern : Twelve) : d1445 (change pattern 8 5) = d2390 pattern := by
  change (if pattern.h then d1280 (change pattern 8 5) else d1444 (change pattern 8 5)) = d2390 pattern
  rw [s2841, s2839]
  rfl
theorem s2843 (pattern : Twelve) : d1448 (change pattern 8 5) = d2390 pattern := by
  change d1445 (change pattern 8 5) = d2390 pattern
  exact s2842 pattern
theorem s2844 (pattern : Twelve) : d1449 (change pattern 8 5) = d6 pattern := by
  change d6 (change pattern 8 5) = d6 pattern
  exact s2764 pattern
theorem s2845 (pattern : Twelve) : d1455 (change pattern 8 5) = d2391 pattern := by
  change (if pattern.e then d1449 (change pattern 8 5) else d1448 (change pattern 8 5)) = d2391 pattern
  rw [s2844, s2843]
  rfl
theorem s2846 (pattern : Twelve) : d1450 (change pattern 8 5) = d2390 pattern := by
  change d1445 (change pattern 8 5) = d2390 pattern
  exact s2842 pattern
theorem s2847 (pattern : Twelve) : d1456 (change pattern 8 5) = d2391 pattern := by
  change (if pattern.e then d1449 (change pattern 8 5) else d1450 (change pattern 8 5)) = d2391 pattern
  rw [s2844, s2846]
  rfl
theorem s2848 (pattern : Twelve) : d1459 (change pattern 8 5) = d2391 pattern := by
  change (if pattern.j then d1456 (change pattern 8 5) else d1455 (change pattern 8 5)) = d2391 pattern
  rw [s2847, s2845]
  simp only [ite_self]
theorem s2849 (pattern : Twelve) : d1463 (change pattern 8 5) = d2391 pattern := by
  change (if pattern.d then d1456 (change pattern 8 5) else d1459 (change pattern 8 5)) = d2391 pattern
  rw [s2847, s2848]
  simp only [ite_self]
end NetHack.Sokoban21.Diagram
