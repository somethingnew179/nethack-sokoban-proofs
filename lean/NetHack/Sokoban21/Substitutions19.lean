/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions18
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s2850 (pattern : Twelve) : d1276 (change pattern 8 5) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 8 5) else d9 (change pattern 8 5)) = d1276 pattern
  rw [s2773, s2747]
  rfl
theorem s2851 (pattern : Twelve) : d1330 (change pattern 8 5) = d1276 pattern := by
  change d1276 (change pattern 8 5) = d1276 pattern
  exact s2850 pattern
theorem s2852 (pattern : Twelve) : d1446 (change pattern 8 5) = d2392 pattern := by
  change (if pattern.h then d125 (change pattern 8 5) else d1330 (change pattern 8 5)) = d2392 pattern
  rw [s2775, s2851]
  rfl
theorem s2853 (pattern : Twelve) : d1451 (change pattern 8 5) = d2392 pattern := by
  change d1446 (change pattern 8 5) = d2392 pattern
  exact s2852 pattern
theorem s2854 (pattern : Twelve) : d1452 (change pattern 8 5) = d6 pattern := by
  change d6 (change pattern 8 5) = d6 pattern
  exact s2764 pattern
theorem s2855 (pattern : Twelve) : d1457 (change pattern 8 5) = d2393 pattern := by
  change (if pattern.e then d1452 (change pattern 8 5) else d1451 (change pattern 8 5)) = d2393 pattern
  rw [s2854, s2853]
  rfl
theorem s2856 (pattern : Twelve) : d1460 (change pattern 8 5) = d2394 pattern := by
  change (if pattern.j then d1457 (change pattern 8 5) else d1456 (change pattern 8 5)) = d2394 pattern
  rw [s2855, s2847]
  rfl
theorem s2857 (pattern : Twelve) : d1461 (change pattern 8 5) = d2395 pattern := by
  change (if pattern.j then d6 (change pattern 8 5) else d1456 (change pattern 8 5)) = d2395 pattern
  rw [s2764, s2847]
  rfl
theorem s2858 (pattern : Twelve) : d1464 (change pattern 8 5) = d2396 pattern := by
  change (if pattern.d then d1461 (change pattern 8 5) else d1460 (change pattern 8 5)) = d2396 pattern
  rw [s2857, s2856]
  rfl
theorem s2859 (pattern : Twelve) : d1466 (change pattern 8 5) = d2397 pattern := by
  change (if pattern.c then d1464 (change pattern 8 5) else d1463 (change pattern 8 5)) = d2397 pattern
  rw [s2858, s2849]
  rfl
theorem s2860 (pattern : Twelve) : d1467 (change pattern 8 5) = d2397 pattern := by
  change (if pattern.c then d1464 (change pattern 8 5) else d1456 (change pattern 8 5)) = d2397 pattern
  rw [s2858, s2847]
  rfl
theorem s2861 (pattern : Twelve) : d1469 (change pattern 8 5) = d2397 pattern := by
  change (if pattern.g then d1467 (change pattern 8 5) else d1466 (change pattern 8 5)) = d2397 pattern
  rw [s2860, s2859]
  simp only [ite_self]
theorem s2862 (pattern : Twelve) : d1470 (change pattern 8 5) = d2397 pattern := by
  change (if pattern.b then d1467 (change pattern 8 5) else d1469 (change pattern 8 5)) = d2397 pattern
  rw [s2860, s2861]
  simp only [ite_self]
theorem s2863 (pattern : Twelve) : d1277 (change pattern 8 5) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 8 5) else d15 (change pattern 8 5)) = d1277 pattern
  rw [s2810, s2825]
  rfl
theorem s2864 (pattern : Twelve) : d1331 (change pattern 8 5) = d1277 pattern := by
  change d1277 (change pattern 8 5) = d1277 pattern
  exact s2863 pattern
theorem s2865 (pattern : Twelve) : d1337 (change pattern 8 5) = d2398 pattern := by
  change (if pattern.h then d1331 (change pattern 8 5) else d1330 (change pattern 8 5)) = d2398 pattern
  rw [s2864, s2851]
  rfl
theorem s2866 (pattern : Twelve) : d1453 (change pattern 8 5) = d2398 pattern := by
  change d1337 (change pattern 8 5) = d2398 pattern
  exact s2865 pattern
theorem s2867 (pattern : Twelve) : d1454 (change pattern 8 5) = d6 pattern := by
  change d6 (change pattern 8 5) = d6 pattern
  exact s2764 pattern
theorem s2868 (pattern : Twelve) : d1458 (change pattern 8 5) = d2399 pattern := by
  change (if pattern.e then d1454 (change pattern 8 5) else d1453 (change pattern 8 5)) = d2399 pattern
  rw [s2867, s2866]
  rfl
theorem s2869 (pattern : Twelve) : d1462 (change pattern 8 5) = d2400 pattern := by
  change (if pattern.j then d1458 (change pattern 8 5) else d1456 (change pattern 8 5)) = d2400 pattern
  rw [s2868, s2847]
  rfl
theorem s2870 (pattern : Twelve) : d1465 (change pattern 8 5) = d2401 pattern := by
  change (if pattern.d then d1461 (change pattern 8 5) else d1462 (change pattern 8 5)) = d2401 pattern
  rw [s2857, s2869]
  rfl
theorem s2871 (pattern : Twelve) : d1468 (change pattern 8 5) = d2402 pattern := by
  change (if pattern.c then d1465 (change pattern 8 5) else d1456 (change pattern 8 5)) = d2402 pattern
  rw [s2870, s2847]
  rfl
theorem s2872 (pattern : Twelve) : d1471 (change pattern 8 5) = d2403 pattern := by
  change (if pattern.a then d1468 (change pattern 8 5) else d1470 (change pattern 8 5)) = d2403 pattern
  rw [s2871, s2862]
  rfl
theorem s2873 (pattern : Twelve) : d1324 (change pattern 8 5) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 8 5) else d11 (change pattern 8 5)) = d1324 pattern
  rw [s2753, s2720]
  rfl
theorem s2874 (pattern : Twelve) : d1645 (change pattern 8 5) = d1324 pattern := by
  change d1324 (change pattern 8 5) = d1324 pattern
  exact s2873 pattern
theorem s2875 (pattern : Twelve) : d1716 (change pattern 8 5) = d1324 pattern := by
  change d1645 (change pattern 8 5) = d1324 pattern
  exact s2874 pattern
theorem s2876 (pattern : Twelve) : d1719 (change pattern 8 5) = d2404 pattern := by
  change (if pattern.e then d1452 (change pattern 8 5) else d1716 (change pattern 8 5)) = d2404 pattern
  rw [s2854, s2875]
  rfl
theorem s2877 (pattern : Twelve) : d1717 (change pattern 8 5) = d20 pattern := by
  change d128 (change pattern 8 5) = d20 pattern
  exact s2780 pattern
theorem s2878 (pattern : Twelve) : d1655 (change pattern 8 5) = d6 pattern := by
  change d6 (change pattern 8 5) = d6 pattern
  exact s2764 pattern
theorem s2879 (pattern : Twelve) : d1720 (change pattern 8 5) = d2405 pattern := by
  change (if pattern.e then d1655 (change pattern 8 5) else d1717 (change pattern 8 5)) = d2405 pattern
  rw [s2878, s2877]
  rfl
theorem s2880 (pattern : Twelve) : d1722 (change pattern 8 5) = d2406 pattern := by
  change (if pattern.j then d1720 (change pattern 8 5) else d1719 (change pattern 8 5)) = d2406 pattern
  rw [s2879, s2876]
  rfl
theorem s2881 (pattern : Twelve) : d1723 (change pattern 8 5) = d2407 pattern := by
  change (if pattern.j then d6 (change pattern 8 5) else d1719 (change pattern 8 5)) = d2407 pattern
  rw [s2764, s2876]
  rfl
theorem s2882 (pattern : Twelve) : d1725 (change pattern 8 5) = d2408 pattern := by
  change (if pattern.d then d1723 (change pattern 8 5) else d1722 (change pattern 8 5)) = d2408 pattern
  rw [s2881, s2880]
  rfl
theorem s2883 (pattern : Twelve) : d1727 (change pattern 8 5) = d2409 pattern := by
  change (if pattern.c then d1725 (change pattern 8 5) else d1719 (change pattern 8 5)) = d2409 pattern
  rw [s2882, s2876]
  rfl
theorem s2884 (pattern : Twelve) : d22 (change pattern 8 5) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 8 5) else d14 (change pattern 8 5)) = d22 pattern
  rw [s2764, s2810]
  rfl
theorem s2885 (pattern : Twelve) : d183 (change pattern 8 5) = d22 pattern := by
  change d22 (change pattern 8 5) = d22 pattern
  exact s2884 pattern
theorem s2886 (pattern : Twelve) : d1667 (change pattern 8 5) = d2410 pattern := by
  change (if pattern.h then d183 (change pattern 8 5) else d128 (change pattern 8 5)) = d2410 pattern
  rw [s2885, s2780]
  rfl
theorem s2887 (pattern : Twelve) : d1718 (change pattern 8 5) = d2410 pattern := by
  change d1667 (change pattern 8 5) = d2410 pattern
  exact s2886 pattern
theorem s2888 (pattern : Twelve) : d1626 (change pattern 8 5) = d6 pattern := by
  change d6 (change pattern 8 5) = d6 pattern
  exact s2764 pattern
theorem s2889 (pattern : Twelve) : d1721 (change pattern 8 5) = d2411 pattern := by
  change (if pattern.e then d1626 (change pattern 8 5) else d1718 (change pattern 8 5)) = d2411 pattern
  rw [s2888, s2887]
  rfl
theorem s2890 (pattern : Twelve) : d1724 (change pattern 8 5) = d2412 pattern := by
  change (if pattern.j then d1721 (change pattern 8 5) else d1719 (change pattern 8 5)) = d2412 pattern
  rw [s2889, s2876]
  rfl
theorem s2891 (pattern : Twelve) : d1726 (change pattern 8 5) = d2413 pattern := by
  change (if pattern.d then d1723 (change pattern 8 5) else d1724 (change pattern 8 5)) = d2413 pattern
  rw [s2881, s2890]
  rfl
theorem s2892 (pattern : Twelve) : d1728 (change pattern 8 5) = d2414 pattern := by
  change (if pattern.c then d1726 (change pattern 8 5) else d1719 (change pattern 8 5)) = d2414 pattern
  rw [s2891, s2876]
  rfl
theorem s2893 (pattern : Twelve) : d1729 (change pattern 8 5) = d2415 pattern := by
  change (if pattern.a then d1728 (change pattern 8 5) else d1727 (change pattern 8 5)) = d2415 pattern
  rw [s2892, s2883]
  rfl
theorem s2894 (pattern : Twelve) : d0 (change pattern 8 12) = d0 pattern := by
  rfl
theorem s2895 (pattern : Twelve) : d26 (change pattern 8 12) = d0 pattern := by
  change d0 (change pattern 8 12) = d0 pattern
  exact s2894 pattern
theorem s2896 (pattern : Twelve) : d171 (change pattern 8 12) = d0 pattern := by
  change d0 (change pattern 8 12) = d0 pattern
  exact s2894 pattern
theorem s2897 (pattern : Twelve) : d184 (change pattern 8 12) = d0 pattern := by
  change (if pattern.h then d171 (change pattern 8 12) else d26 (change pattern 8 12)) = d0 pattern
  rw [s2896, s2895]
  simp only [ite_self]
theorem s2898 (pattern : Twelve) : d1 (change pattern 8 12) = d1 pattern := by
  rfl
theorem s2899 (pattern : Twelve) : d7 (change pattern 8 12) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 8 12) else d0 (change pattern 8 12)) = d7 pattern
  rw [s2898, s2894]
  rfl
theorem s2900 (pattern : Twelve) : d17 (change pattern 8 12) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 8 12) else d0 (change pattern 8 12)) = d17 pattern
  rw [s2899, s2894]
  rfl
theorem s2901 (pattern : Twelve) : d366 (change pattern 8 12) = d17 pattern := by
  change d17 (change pattern 8 12) = d17 pattern
  exact s2900 pattern
theorem s2902 (pattern : Twelve) : d372 (change pattern 8 12) = d2357 pattern := by
  change (if pattern.h then d366 (change pattern 8 12) else d171 (change pattern 8 12)) = d2357 pattern
  rw [s2901, s2896]
  rfl
theorem s2903 (pattern : Twelve) : d389 (change pattern 8 12) = d2416 pattern := by
  change (if pattern.f then d372 (change pattern 8 12) else d184 (change pattern 8 12)) = d2416 pattern
  rw [s2902, s2897]
  rfl
theorem s2904 (pattern : Twelve) : d367 (change pattern 8 12) = d0 pattern := by
  change d0 (change pattern 8 12) = d0 pattern
  exact s2894 pattern
theorem s2905 (pattern : Twelve) : d373 (change pattern 8 12) = d0 pattern := by
  change (if pattern.h then d367 (change pattern 8 12) else d171 (change pattern 8 12)) = d0 pattern
  rw [s2904, s2896]
  simp only [ite_self]
theorem s2906 (pattern : Twelve) : d2 (change pattern 8 12) = d2 pattern := by
  rfl
theorem s2907 (pattern : Twelve) : d10 (change pattern 8 12) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 8 12) else d0 (change pattern 8 12)) = d10 pattern
  rw [s2906, s2894]
  rfl
theorem s2908 (pattern : Twelve) : d3 (change pattern 8 12) = d3 pattern := by
  rfl
theorem s2909 (pattern : Twelve) : d11 (change pattern 8 12) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 8 12) else d1 (change pattern 8 12)) = d11 pattern
  rw [s2908, s2898]
  rfl
theorem s2910 (pattern : Twelve) : d19 (change pattern 8 12) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 8 12) else d10 (change pattern 8 12)) = d19 pattern
  rw [s2909, s2907]
  rfl
theorem s2911 (pattern : Twelve) : d29 (change pattern 8 12) = d19 pattern := by
  change d19 (change pattern 8 12) = d19 pattern
  exact s2910 pattern
theorem s2912 (pattern : Twelve) : d374 (change pattern 8 12) = d2358 pattern := by
  change (if pattern.h then d29 (change pattern 8 12) else d366 (change pattern 8 12)) = d2358 pattern
  rw [s2911, s2901]
  rfl
theorem s2913 (pattern : Twelve) : d390 (change pattern 8 12) = d2417 pattern := by
  change (if pattern.f then d374 (change pattern 8 12) else d373 (change pattern 8 12)) = d2417 pattern
  rw [s2912, s2905]
  rfl
theorem s2914 (pattern : Twelve) : d402 (change pattern 8 12) = d2418 pattern := by
  change (if pattern.e then d390 (change pattern 8 12) else d389 (change pattern 8 12)) = d2418 pattern
  rw [s2913, s2903]
  rfl
theorem s2915 (pattern : Twelve) : d368 (change pattern 8 12) = d0 pattern := by
  change d0 (change pattern 8 12) = d0 pattern
  exact s2894 pattern
theorem s2916 (pattern : Twelve) : d369 (change pattern 8 12) = d0 pattern := by
  change d0 (change pattern 8 12) = d0 pattern
  exact s2894 pattern
theorem s2917 (pattern : Twelve) : d375 (change pattern 8 12) = d0 pattern := by
  change (if pattern.h then d369 (change pattern 8 12) else d368 (change pattern 8 12)) = d0 pattern
  rw [s2916, s2915]
  simp only [ite_self]
theorem s2918 (pattern : Twelve) : d36 (change pattern 8 12) = d17 pattern := by
  change d17 (change pattern 8 12) = d17 pattern
  exact s2900 pattern
theorem s2919 (pattern : Twelve) : d376 (change pattern 8 12) = d2357 pattern := by
  change (if pattern.h then d36 (change pattern 8 12) else d369 (change pattern 8 12)) = d2357 pattern
  rw [s2918, s2916]
  rfl
theorem s2920 (pattern : Twelve) : d391 (change pattern 8 12) = d2416 pattern := by
  change (if pattern.f then d376 (change pattern 8 12) else d375 (change pattern 8 12)) = d2416 pattern
  rw [s2919, s2917]
  rfl
theorem s2921 (pattern : Twelve) : d35 (change pattern 8 12) = d0 pattern := by
  change d0 (change pattern 8 12) = d0 pattern
  exact s2894 pattern
theorem s2922 (pattern : Twelve) : d377 (change pattern 8 12) = d0 pattern := by
  change (if pattern.h then d35 (change pattern 8 12) else d369 (change pattern 8 12)) = d0 pattern
  rw [s2921, s2916]
  simp only [ite_self]
theorem s2923 (pattern : Twelve) : d378 (change pattern 8 12) = d2358 pattern := by
  change (if pattern.h then d29 (change pattern 8 12) else d36 (change pattern 8 12)) = d2358 pattern
  rw [s2911, s2918]
  rfl
theorem s2924 (pattern : Twelve) : d392 (change pattern 8 12) = d2417 pattern := by
  change (if pattern.f then d378 (change pattern 8 12) else d377 (change pattern 8 12)) = d2417 pattern
  rw [s2923, s2922]
  rfl
theorem s2925 (pattern : Twelve) : d403 (change pattern 8 12) = d2418 pattern := by
  change (if pattern.e then d392 (change pattern 8 12) else d391 (change pattern 8 12)) = d2418 pattern
  rw [s2924, s2920]
  rfl
theorem s2926 (pattern : Twelve) : d409 (change pattern 8 12) = d2418 pattern := by
  change (if pattern.j then d403 (change pattern 8 12) else d402 (change pattern 8 12)) = d2418 pattern
  rw [s2925, s2914]
  simp only [ite_self]
theorem s2927 (pattern : Twelve) : d33 (change pattern 8 12) = d0 pattern := by
  change d0 (change pattern 8 12) = d0 pattern
  exact s2894 pattern
theorem s2928 (pattern : Twelve) : d379 (change pattern 8 12) = d0 pattern := by
  change (if pattern.h then d35 (change pattern 8 12) else d33 (change pattern 8 12)) = d0 pattern
  rw [s2921, s2927]
  simp only [ite_self]
theorem s2929 (pattern : Twelve) : d380 (change pattern 8 12) = d2357 pattern := by
  change (if pattern.h then d36 (change pattern 8 12) else d35 (change pattern 8 12)) = d2357 pattern
  rw [s2918, s2921]
  rfl
theorem s2930 (pattern : Twelve) : d393 (change pattern 8 12) = d2416 pattern := by
  change (if pattern.f then d380 (change pattern 8 12) else d379 (change pattern 8 12)) = d2416 pattern
  rw [s2929, s2928]
  rfl
theorem s2931 (pattern : Twelve) : d394 (change pattern 8 12) = d2417 pattern := by
  change (if pattern.f then d378 (change pattern 8 12) else d35 (change pattern 8 12)) = d2417 pattern
  rw [s2923, s2921]
  rfl
theorem s2932 (pattern : Twelve) : d404 (change pattern 8 12) = d2418 pattern := by
  change (if pattern.e then d394 (change pattern 8 12) else d393 (change pattern 8 12)) = d2418 pattern
  rw [s2931, s2930]
  rfl
theorem s2933 (pattern : Twelve) : d410 (change pattern 8 12) = d2418 pattern := by
  change (if pattern.j then d404 (change pattern 8 12) else d403 (change pattern 8 12)) = d2418 pattern
  rw [s2932, s2925]
  simp only [ite_self]
theorem s2934 (pattern : Twelve) : d415 (change pattern 8 12) = d2418 pattern := by
  change (if pattern.d then d410 (change pattern 8 12) else d409 (change pattern 8 12)) = d2418 pattern
  rw [s2933, s2926]
  simp only [ite_self]
theorem s2935 (pattern : Twelve) : d370 (change pattern 8 12) = d0 pattern := by
  change d0 (change pattern 8 12) = d0 pattern
  exact s2894 pattern
theorem s2936 (pattern : Twelve) : d371 (change pattern 8 12) = d0 pattern := by
  change d0 (change pattern 8 12) = d0 pattern
  exact s2894 pattern
theorem s2937 (pattern : Twelve) : d381 (change pattern 8 12) = d0 pattern := by
  change (if pattern.h then d371 (change pattern 8 12) else d370 (change pattern 8 12)) = d0 pattern
  rw [s2936, s2935]
  simp only [ite_self]
theorem s2938 (pattern : Twelve) : d382 (change pattern 8 12) = d2357 pattern := by
  change (if pattern.h then d36 (change pattern 8 12) else d371 (change pattern 8 12)) = d2357 pattern
  rw [s2918, s2936]
  rfl
theorem s2939 (pattern : Twelve) : d395 (change pattern 8 12) = d2416 pattern := by
  change (if pattern.f then d382 (change pattern 8 12) else d381 (change pattern 8 12)) = d2416 pattern
  rw [s2938, s2937]
  rfl
theorem s2940 (pattern : Twelve) : d383 (change pattern 8 12) = d0 pattern := by
  change (if pattern.h then d35 (change pattern 8 12) else d371 (change pattern 8 12)) = d0 pattern
  rw [s2921, s2936]
  simp only [ite_self]
theorem s2941 (pattern : Twelve) : d396 (change pattern 8 12) = d2417 pattern := by
  change (if pattern.f then d378 (change pattern 8 12) else d383 (change pattern 8 12)) = d2417 pattern
  rw [s2923, s2940]
  rfl
theorem s2942 (pattern : Twelve) : d405 (change pattern 8 12) = d2418 pattern := by
  change (if pattern.e then d396 (change pattern 8 12) else d395 (change pattern 8 12)) = d2418 pattern
  rw [s2941, s2939]
  rfl
theorem s2943 (pattern : Twelve) : d39 (change pattern 8 12) = d2 pattern := by
  change d2 (change pattern 8 12) = d2 pattern
  exact s2906 pattern
theorem s2944 (pattern : Twelve) : d9 (change pattern 8 12) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 8 12) else d2 (change pattern 8 12)) = d9 pattern
  rw [s2908, s2906]
  rfl
theorem s2945 (pattern : Twelve) : d23 (change pattern 8 12) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 8 12) else d2 (change pattern 8 12)) = d23 pattern
  rw [s2944, s2906]
  rfl
theorem s2946 (pattern : Twelve) : d40 (change pattern 8 12) = d23 pattern := by
  change d23 (change pattern 8 12) = d23 pattern
  exact s2945 pattern
theorem s2947 (pattern : Twelve) : d384 (change pattern 8 12) = d2360 pattern := by
  change (if pattern.h then d40 (change pattern 8 12) else d39 (change pattern 8 12)) = d2360 pattern
  rw [s2946, s2943]
  rfl
theorem s2948 (pattern : Twelve) : d397 (change pattern 8 12) = d2419 pattern := by
  change (if pattern.f then d384 (change pattern 8 12) else d39 (change pattern 8 12)) = d2419 pattern
  rw [s2947, s2943]
  rfl
theorem s2949 (pattern : Twelve) : d4 (change pattern 8 12) = d4 pattern := by
  rfl
theorem s2950 (pattern : Twelve) : d16 (change pattern 8 12) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 8 12) else d2 (change pattern 8 12)) = d16 pattern
  rw [s2949, s2906]
  rfl
theorem s2951 (pattern : Twelve) : d5 (change pattern 8 12) = d5 pattern := by
  rfl
theorem s2952 (pattern : Twelve) : d12 (change pattern 8 12) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 8 12) else d3 (change pattern 8 12)) = d12 pattern
  rw [s2951, s2908]
  rfl
theorem s2953 (pattern : Twelve) : d25 (change pattern 8 12) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 8 12) else d16 (change pattern 8 12)) = d25 pattern
  rw [s2952, s2950]
  rfl
theorem s2954 (pattern : Twelve) : d42 (change pattern 8 12) = d25 pattern := by
  change d25 (change pattern 8 12) = d25 pattern
  exact s2953 pattern
theorem s2955 (pattern : Twelve) : d385 (change pattern 8 12) = d2361 pattern := by
  change (if pattern.h then d42 (change pattern 8 12) else d40 (change pattern 8 12)) = d2361 pattern
  rw [s2954, s2946]
  rfl
theorem s2956 (pattern : Twelve) : d398 (change pattern 8 12) = d2420 pattern := by
  change (if pattern.f then d385 (change pattern 8 12) else d39 (change pattern 8 12)) = d2420 pattern
  rw [s2955, s2943]
  rfl
theorem s2957 (pattern : Twelve) : d406 (change pattern 8 12) = d2421 pattern := by
  change (if pattern.e then d398 (change pattern 8 12) else d397 (change pattern 8 12)) = d2421 pattern
  rw [s2956, s2948]
  rfl
theorem s2958 (pattern : Twelve) : d411 (change pattern 8 12) = d2422 pattern := by
  change (if pattern.j then d406 (change pattern 8 12) else d405 (change pattern 8 12)) = d2422 pattern
  rw [s2957, s2942]
  rfl
theorem s2959 (pattern : Twelve) : d399 (change pattern 8 12) = d2416 pattern := by
  change (if pattern.f then d380 (change pattern 8 12) else d35 (change pattern 8 12)) = d2416 pattern
  rw [s2929, s2921]
  rfl
theorem s2960 (pattern : Twelve) : d407 (change pattern 8 12) = d2418 pattern := by
  change (if pattern.e then d394 (change pattern 8 12) else d399 (change pattern 8 12)) = d2418 pattern
  rw [s2931, s2959]
  rfl
theorem s2961 (pattern : Twelve) : d6 (change pattern 8 12) = d6 pattern := by
  rfl
theorem s2962 (pattern : Twelve) : d412 (change pattern 8 12) = d2423 pattern := by
  change (if pattern.j then d6 (change pattern 8 12) else d407 (change pattern 8 12)) = d2423 pattern
  rw [s2961, s2960]
  rfl
theorem s2963 (pattern : Twelve) : d416 (change pattern 8 12) = d2424 pattern := by
  change (if pattern.d then d412 (change pattern 8 12) else d411 (change pattern 8 12)) = d2424 pattern
  rw [s2962, s2958]
  rfl
theorem s2964 (pattern : Twelve) : d419 (change pattern 8 12) = d2425 pattern := by
  change (if pattern.c then d416 (change pattern 8 12) else d415 (change pattern 8 12)) = d2425 pattern
  rw [s2963, s2934]
  rfl
theorem s2965 (pattern : Twelve) : d413 (change pattern 8 12) = d2422 pattern := by
  change (if pattern.j then d406 (change pattern 8 12) else d407 (change pattern 8 12)) = d2422 pattern
  rw [s2957, s2960]
  rfl
theorem s2966 (pattern : Twelve) : d417 (change pattern 8 12) = d2424 pattern := by
  change (if pattern.d then d412 (change pattern 8 12) else d413 (change pattern 8 12)) = d2424 pattern
  rw [s2962, s2965]
  rfl
theorem s2967 (pattern : Twelve) : d420 (change pattern 8 12) = d2425 pattern := by
  change (if pattern.c then d417 (change pattern 8 12) else d407 (change pattern 8 12)) = d2425 pattern
  rw [s2966, s2960]
  rfl
theorem s2968 (pattern : Twelve) : d422 (change pattern 8 12) = d2425 pattern := by
  change (if pattern.g then d420 (change pattern 8 12) else d419 (change pattern 8 12)) = d2425 pattern
  rw [s2967, s2964]
  simp only [ite_self]
theorem s2969 (pattern : Twelve) : d423 (change pattern 8 12) = d2425 pattern := by
  change (if pattern.b then d420 (change pattern 8 12) else d422 (change pattern 8 12)) = d2425 pattern
  rw [s2967, s2968]
  simp only [ite_self]
theorem s2970 (pattern : Twelve) : d117 (change pattern 8 12) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 8 12) else d3 (change pattern 8 12)) = d117 pattern
  rw [s2949, s2908]
  rfl
theorem s2971 (pattern : Twelve) : d119 (change pattern 8 12) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 8 12) else d3 (change pattern 8 12)) = d119 pattern
  rw [s2970, s2908]
  rfl
theorem s2972 (pattern : Twelve) : d125 (change pattern 8 12) = d119 pattern := by
  change d119 (change pattern 8 12) = d119 pattern
  exact s2971 pattern
theorem s2973 (pattern : Twelve) : d386 (change pattern 8 12) = d2367 pattern := by
  change (if pattern.h then d125 (change pattern 8 12) else d39 (change pattern 8 12)) = d2367 pattern
  rw [s2972, s2943]
  rfl
theorem s2974 (pattern : Twelve) : d400 (change pattern 8 12) = d2426 pattern := by
  change (if pattern.f then d386 (change pattern 8 12) else d39 (change pattern 8 12)) = d2426 pattern
  rw [s2973, s2943]
  rfl
theorem s2975 (pattern : Twelve) : d47 (change pattern 8 12) = d3 pattern := by
  change d3 (change pattern 8 12) = d3 pattern
  exact s2908 pattern
theorem s2976 (pattern : Twelve) : d387 (change pattern 8 12) = d2427 pattern := by
  change (if pattern.h then d47 (change pattern 8 12) else d39 (change pattern 8 12)) = d2427 pattern
  rw [s2975, s2943]
  rfl
theorem s2977 (pattern : Twelve) : d13 (change pattern 8 12) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 8 12) else d4 (change pattern 8 12)) = d13 pattern
  rw [s2961, s2949]
  rfl
theorem s2978 (pattern : Twelve) : d20 (change pattern 8 12) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 8 12) else d12 (change pattern 8 12)) = d20 pattern
  rw [s2977, s2952]
  rfl
theorem s2979 (pattern : Twelve) : d128 (change pattern 8 12) = d20 pattern := by
  change d20 (change pattern 8 12) = d20 pattern
  exact s2978 pattern
theorem s2980 (pattern : Twelve) : d388 (change pattern 8 12) = d2368 pattern := by
  change (if pattern.h then d128 (change pattern 8 12) else d40 (change pattern 8 12)) = d2368 pattern
  rw [s2979, s2946]
  rfl
theorem s2981 (pattern : Twelve) : d401 (change pattern 8 12) = d2428 pattern := by
  change (if pattern.f then d388 (change pattern 8 12) else d387 (change pattern 8 12)) = d2428 pattern
  rw [s2980, s2976]
  rfl
theorem s2982 (pattern : Twelve) : d408 (change pattern 8 12) = d2429 pattern := by
  change (if pattern.e then d401 (change pattern 8 12) else d400 (change pattern 8 12)) = d2429 pattern
  rw [s2981, s2974]
  rfl
theorem s2983 (pattern : Twelve) : d414 (change pattern 8 12) = d2430 pattern := by
  change (if pattern.j then d408 (change pattern 8 12) else d407 (change pattern 8 12)) = d2430 pattern
  rw [s2982, s2960]
  rfl
theorem s2984 (pattern : Twelve) : d418 (change pattern 8 12) = d2431 pattern := by
  change (if pattern.d then d412 (change pattern 8 12) else d414 (change pattern 8 12)) = d2431 pattern
  rw [s2962, s2983]
  rfl
theorem s2985 (pattern : Twelve) : d421 (change pattern 8 12) = d2432 pattern := by
  change (if pattern.c then d418 (change pattern 8 12) else d407 (change pattern 8 12)) = d2432 pattern
  rw [s2984, s2960]
  rfl
theorem s2986 (pattern : Twelve) : d424 (change pattern 8 12) = d2433 pattern := by
  change (if pattern.a then d421 (change pattern 8 12) else d423 (change pattern 8 12)) = d2433 pattern
  rw [s2985, s2969]
  rfl
theorem s2987 (pattern : Twelve) : d814 (change pattern 8 12) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 8 12) else d7 (change pattern 8 12)) = d814 pattern
  rw [s2898, s2899]
  rfl
theorem s2988 (pattern : Twelve) : d818 (change pattern 8 12) = d814 pattern := by
  change d814 (change pattern 8 12) = d814 pattern
  exact s2987 pattern
theorem s2989 (pattern : Twelve) : d1030 (change pattern 8 12) = d2374 pattern := by
  change (if pattern.h then d818 (change pattern 8 12) else d366 (change pattern 8 12)) = d2374 pattern
  rw [s2988, s2901]
  rfl
theorem s2990 (pattern : Twelve) : d1038 (change pattern 8 12) = d2434 pattern := by
  change (if pattern.f then d1030 (change pattern 8 12) else d373 (change pattern 8 12)) = d2434 pattern
  rw [s2989, s2905]
  rfl
theorem s2991 (pattern : Twelve) : d1031 (change pattern 8 12) = d17 pattern := by
  change (if pattern.h then d36 (change pattern 8 12) else d366 (change pattern 8 12)) = d17 pattern
  rw [s2918, s2901]
  simp only [ite_self]
theorem s2992 (pattern : Twelve) : d1032 (change pattern 8 12) = d2375 pattern := by
  change (if pattern.h then d42 (change pattern 8 12) else d29 (change pattern 8 12)) = d2375 pattern
  rw [s2954, s2911]
  rfl
theorem s2993 (pattern : Twelve) : d1039 (change pattern 8 12) = d2435 pattern := by
  change (if pattern.f then d1032 (change pattern 8 12) else d1031 (change pattern 8 12)) = d2435 pattern
  rw [s2992, s2991]
  rfl
theorem s2994 (pattern : Twelve) : d1048 (change pattern 8 12) = d2436 pattern := by
  change (if pattern.e then d1039 (change pattern 8 12) else d1038 (change pattern 8 12)) = d2436 pattern
  rw [s2993, s2990]
  rfl
theorem s2995 (pattern : Twelve) : d1033 (change pattern 8 12) = d2374 pattern := by
  change (if pattern.h then d818 (change pattern 8 12) else d36 (change pattern 8 12)) = d2374 pattern
  rw [s2988, s2918]
  rfl
theorem s2996 (pattern : Twelve) : d1040 (change pattern 8 12) = d2434 pattern := by
  change (if pattern.f then d1033 (change pattern 8 12) else d377 (change pattern 8 12)) = d2434 pattern
  rw [s2995, s2922]
  rfl
theorem s2997 (pattern : Twelve) : d1041 (change pattern 8 12) = d2435 pattern := by
  change (if pattern.f then d1032 (change pattern 8 12) else d36 (change pattern 8 12)) = d2435 pattern
  rw [s2992, s2918]
  rfl
theorem s2998 (pattern : Twelve) : d1049 (change pattern 8 12) = d2436 pattern := by
  change (if pattern.e then d1041 (change pattern 8 12) else d1040 (change pattern 8 12)) = d2436 pattern
  rw [s2997, s2996]
  rfl
theorem s2999 (pattern : Twelve) : d1054 (change pattern 8 12) = d2436 pattern := by
  change (if pattern.j then d1049 (change pattern 8 12) else d1048 (change pattern 8 12)) = d2436 pattern
  rw [s2998, s2994]
  simp only [ite_self]
end NetHack.Sokoban21.Diagram
