/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions19
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s3000 (pattern : Twelve) : d1042 (change pattern 8 12) = d2434 pattern := by
  change (if pattern.f then d1033 (change pattern 8 12) else d35 (change pattern 8 12)) = d2434 pattern
  rw [s2995, s2921]
  rfl
theorem s3001 (pattern : Twelve) : d1050 (change pattern 8 12) = d2436 pattern := by
  change (if pattern.e then d1041 (change pattern 8 12) else d1042 (change pattern 8 12)) = d2436 pattern
  rw [s2997, s3000]
  rfl
theorem s3002 (pattern : Twelve) : d1055 (change pattern 8 12) = d2436 pattern := by
  change (if pattern.j then d1050 (change pattern 8 12) else d1049 (change pattern 8 12)) = d2436 pattern
  rw [s3001, s2998]
  simp only [ite_self]
theorem s3003 (pattern : Twelve) : d1060 (change pattern 8 12) = d2436 pattern := by
  change (if pattern.d then d1055 (change pattern 8 12) else d1054 (change pattern 8 12)) = d2436 pattern
  rw [s3002, s2999]
  simp only [ite_self]
theorem s3004 (pattern : Twelve) : d1043 (change pattern 8 12) = d2434 pattern := by
  change (if pattern.f then d1033 (change pattern 8 12) else d383 (change pattern 8 12)) = d2434 pattern
  rw [s2995, s2940]
  rfl
theorem s3005 (pattern : Twelve) : d1051 (change pattern 8 12) = d2436 pattern := by
  change (if pattern.e then d1041 (change pattern 8 12) else d1043 (change pattern 8 12)) = d2436 pattern
  rw [s2997, s3004]
  rfl
theorem s3006 (pattern : Twelve) : d815 (change pattern 8 12) = d815 pattern := by
  change (if pattern.k then d3 (change pattern 8 12) else d9 (change pattern 8 12)) = d815 pattern
  rw [s2908, s2944]
  rfl
theorem s3007 (pattern : Twelve) : d820 (change pattern 8 12) = d815 pattern := by
  change d815 (change pattern 8 12) = d815 pattern
  exact s3006 pattern
theorem s3008 (pattern : Twelve) : d1034 (change pattern 8 12) = d2377 pattern := by
  change (if pattern.h then d820 (change pattern 8 12) else d40 (change pattern 8 12)) = d2377 pattern
  rw [s3007, s2946]
  rfl
theorem s3009 (pattern : Twelve) : d1044 (change pattern 8 12) = d2437 pattern := by
  change (if pattern.f then d1034 (change pattern 8 12) else d39 (change pattern 8 12)) = d2437 pattern
  rw [s3008, s2943]
  rfl
theorem s3010 (pattern : Twelve) : d14 (change pattern 8 12) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 8 12) else d5 (change pattern 8 12)) = d14 pattern
  rw [s2961, s2951]
  rfl
theorem s3011 (pattern : Twelve) : d21 (change pattern 8 12) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 8 12) else d13 (change pattern 8 12)) = d21 pattern
  rw [s3010, s2977]
  rfl
theorem s3012 (pattern : Twelve) : d822 (change pattern 8 12) = d21 pattern := by
  change d21 (change pattern 8 12) = d21 pattern
  exact s3011 pattern
theorem s3013 (pattern : Twelve) : d1035 (change pattern 8 12) = d2378 pattern := by
  change (if pattern.h then d822 (change pattern 8 12) else d42 (change pattern 8 12)) = d2378 pattern
  rw [s3012, s2954]
  rfl
theorem s3014 (pattern : Twelve) : d1045 (change pattern 8 12) = d2438 pattern := by
  change (if pattern.f then d1035 (change pattern 8 12) else d40 (change pattern 8 12)) = d2438 pattern
  rw [s3013, s2946]
  rfl
theorem s3015 (pattern : Twelve) : d1052 (change pattern 8 12) = d2439 pattern := by
  change (if pattern.e then d1045 (change pattern 8 12) else d1044 (change pattern 8 12)) = d2439 pattern
  rw [s3014, s3009]
  rfl
theorem s3016 (pattern : Twelve) : d1056 (change pattern 8 12) = d2440 pattern := by
  change (if pattern.j then d1052 (change pattern 8 12) else d1051 (change pattern 8 12)) = d2440 pattern
  rw [s3015, s3005]
  rfl
theorem s3017 (pattern : Twelve) : d1057 (change pattern 8 12) = d2441 pattern := by
  change (if pattern.j then d6 (change pattern 8 12) else d1050 (change pattern 8 12)) = d2441 pattern
  rw [s2961, s3001]
  rfl
theorem s3018 (pattern : Twelve) : d1061 (change pattern 8 12) = d2442 pattern := by
  change (if pattern.d then d1057 (change pattern 8 12) else d1056 (change pattern 8 12)) = d2442 pattern
  rw [s3017, s3016]
  rfl
theorem s3019 (pattern : Twelve) : d1064 (change pattern 8 12) = d2443 pattern := by
  change (if pattern.c then d1061 (change pattern 8 12) else d1060 (change pattern 8 12)) = d2443 pattern
  rw [s3018, s3003]
  rfl
theorem s3020 (pattern : Twelve) : d1058 (change pattern 8 12) = d2440 pattern := by
  change (if pattern.j then d1052 (change pattern 8 12) else d1050 (change pattern 8 12)) = d2440 pattern
  rw [s3015, s3001]
  rfl
theorem s3021 (pattern : Twelve) : d1062 (change pattern 8 12) = d2442 pattern := by
  change (if pattern.d then d1057 (change pattern 8 12) else d1058 (change pattern 8 12)) = d2442 pattern
  rw [s3017, s3020]
  rfl
theorem s3022 (pattern : Twelve) : d1065 (change pattern 8 12) = d2443 pattern := by
  change (if pattern.c then d1062 (change pattern 8 12) else d1050 (change pattern 8 12)) = d2443 pattern
  rw [s3021, s3001]
  rfl
theorem s3023 (pattern : Twelve) : d1067 (change pattern 8 12) = d2443 pattern := by
  change (if pattern.g then d1065 (change pattern 8 12) else d1064 (change pattern 8 12)) = d2443 pattern
  rw [s3022, s3019]
  simp only [ite_self]
theorem s3024 (pattern : Twelve) : d1068 (change pattern 8 12) = d2443 pattern := by
  change (if pattern.b then d1065 (change pattern 8 12) else d1067 (change pattern 8 12)) = d2443 pattern
  rw [s3022, s3023]
  simp only [ite_self]
theorem s3025 (pattern : Twelve) : d15 (change pattern 8 12) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 8 12) else d4 (change pattern 8 12)) = d15 pattern
  rw [s2951, s2949]
  rfl
theorem s3026 (pattern : Twelve) : d873 (change pattern 8 12) = d873 pattern := by
  change (if pattern.k then d15 (change pattern 8 12) else d117 (change pattern 8 12)) = d873 pattern
  rw [s3025, s2970]
  rfl
theorem s3027 (pattern : Twelve) : d880 (change pattern 8 12) = d873 pattern := by
  change d873 (change pattern 8 12) = d873 pattern
  exact s3026 pattern
theorem s3028 (pattern : Twelve) : d1036 (change pattern 8 12) = d2384 pattern := by
  change (if pattern.h then d880 (change pattern 8 12) else d40 (change pattern 8 12)) = d2384 pattern
  rw [s3027, s2946]
  rfl
theorem s3029 (pattern : Twelve) : d1046 (change pattern 8 12) = d2444 pattern := by
  change (if pattern.f then d1036 (change pattern 8 12) else d39 (change pattern 8 12)) = d2444 pattern
  rw [s3028, s2943]
  rfl
theorem s3030 (pattern : Twelve) : d1037 (change pattern 8 12) = d2445 pattern := by
  change (if pattern.h then d125 (change pattern 8 12) else d40 (change pattern 8 12)) = d2445 pattern
  rw [s2972, s2946]
  rfl
theorem s3031 (pattern : Twelve) : d889 (change pattern 8 12) = d1690 pattern := by
  change (if pattern.h then d6 (change pattern 8 12) else d42 (change pattern 8 12)) = d1690 pattern
  rw [s2961, s2954]
  rfl
theorem s3032 (pattern : Twelve) : d1047 (change pattern 8 12) = d2446 pattern := by
  change (if pattern.f then d889 (change pattern 8 12) else d1037 (change pattern 8 12)) = d2446 pattern
  rw [s3031, s3030]
  rfl
theorem s3033 (pattern : Twelve) : d1053 (change pattern 8 12) = d2447 pattern := by
  change (if pattern.e then d1047 (change pattern 8 12) else d1046 (change pattern 8 12)) = d2447 pattern
  rw [s3032, s3029]
  rfl
theorem s3034 (pattern : Twelve) : d1059 (change pattern 8 12) = d2448 pattern := by
  change (if pattern.j then d1053 (change pattern 8 12) else d1050 (change pattern 8 12)) = d2448 pattern
  rw [s3033, s3001]
  rfl
theorem s3035 (pattern : Twelve) : d1063 (change pattern 8 12) = d2449 pattern := by
  change (if pattern.d then d1057 (change pattern 8 12) else d1059 (change pattern 8 12)) = d2449 pattern
  rw [s3017, s3034]
  rfl
theorem s3036 (pattern : Twelve) : d1066 (change pattern 8 12) = d2450 pattern := by
  change (if pattern.c then d1063 (change pattern 8 12) else d1050 (change pattern 8 12)) = d2450 pattern
  rw [s3035, s3001]
  rfl
theorem s3037 (pattern : Twelve) : d1069 (change pattern 8 12) = d2451 pattern := by
  change (if pattern.a then d1066 (change pattern 8 12) else d1068 (change pattern 8 12)) = d2451 pattern
  rw [s3036, s3024]
  rfl
theorem s3038 (pattern : Twelve) : d8 (change pattern 8 12) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 8 12) else d1 (change pattern 8 12)) = d8 pattern
  rw [s2906, s2898]
  rfl
theorem s3039 (pattern : Twelve) : d1275 (change pattern 8 12) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 8 12) else d7 (change pattern 8 12)) = d1275 pattern
  rw [s3038, s2899]
  rfl
theorem s3040 (pattern : Twelve) : d1444 (change pattern 8 12) = d1275 pattern := by
  change d1275 (change pattern 8 12) = d1275 pattern
  exact s3039 pattern
theorem s3041 (pattern : Twelve) : d872 (change pattern 8 12) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 8 12) else d1 (change pattern 8 12)) = d872 pattern
  rw [s3038, s2898]
  rfl
theorem s3042 (pattern : Twelve) : d1280 (change pattern 8 12) = d872 pattern := by
  change d872 (change pattern 8 12) = d872 pattern
  exact s3041 pattern
theorem s3043 (pattern : Twelve) : d1445 (change pattern 8 12) = d2390 pattern := by
  change (if pattern.h then d1280 (change pattern 8 12) else d1444 (change pattern 8 12)) = d2390 pattern
  rw [s3042, s3040]
  rfl
theorem s3044 (pattern : Twelve) : d1448 (change pattern 8 12) = d2452 pattern := by
  change (if pattern.f then d1445 (change pattern 8 12) else d1031 (change pattern 8 12)) = d2452 pattern
  rw [s3043, s2991]
  rfl
theorem s3045 (pattern : Twelve) : d1449 (change pattern 8 12) = d1294 pattern := by
  change (if pattern.f then d6 (change pattern 8 12) else d29 (change pattern 8 12)) = d1294 pattern
  rw [s2961, s2911]
  rfl
theorem s3046 (pattern : Twelve) : d1455 (change pattern 8 12) = d2453 pattern := by
  change (if pattern.e then d1449 (change pattern 8 12) else d1448 (change pattern 8 12)) = d2453 pattern
  rw [s3045, s3044]
  rfl
theorem s3047 (pattern : Twelve) : d1450 (change pattern 8 12) = d2452 pattern := by
  change (if pattern.f then d1445 (change pattern 8 12) else d36 (change pattern 8 12)) = d2452 pattern
  rw [s3043, s2918]
  rfl
theorem s3048 (pattern : Twelve) : d1456 (change pattern 8 12) = d2453 pattern := by
  change (if pattern.e then d1449 (change pattern 8 12) else d1450 (change pattern 8 12)) = d2453 pattern
  rw [s3045, s3047]
  rfl
theorem s3049 (pattern : Twelve) : d1459 (change pattern 8 12) = d2453 pattern := by
  change (if pattern.j then d1456 (change pattern 8 12) else d1455 (change pattern 8 12)) = d2453 pattern
  rw [s3048, s3046]
  simp only [ite_self]
theorem s3050 (pattern : Twelve) : d1463 (change pattern 8 12) = d2453 pattern := by
  change (if pattern.d then d1456 (change pattern 8 12) else d1459 (change pattern 8 12)) = d2453 pattern
  rw [s3048, s3049]
  simp only [ite_self]
theorem s3051 (pattern : Twelve) : d1276 (change pattern 8 12) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 8 12) else d9 (change pattern 8 12)) = d1276 pattern
  rw [s2970, s2944]
  rfl
theorem s3052 (pattern : Twelve) : d1330 (change pattern 8 12) = d1276 pattern := by
  change d1276 (change pattern 8 12) = d1276 pattern
  exact s3051 pattern
theorem s3053 (pattern : Twelve) : d1446 (change pattern 8 12) = d2392 pattern := by
  change (if pattern.h then d125 (change pattern 8 12) else d1330 (change pattern 8 12)) = d2392 pattern
  rw [s2972, s3052]
  rfl
theorem s3054 (pattern : Twelve) : d1451 (change pattern 8 12) = d2454 pattern := by
  change (if pattern.f then d1446 (change pattern 8 12) else d40 (change pattern 8 12)) = d2454 pattern
  rw [s3053, s2946]
  rfl
theorem s3055 (pattern : Twelve) : d1452 (change pattern 8 12) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 8 12) else d42 (change pattern 8 12)) = d1650 pattern
  rw [s2961, s2954]
  rfl
theorem s3056 (pattern : Twelve) : d1457 (change pattern 8 12) = d2455 pattern := by
  change (if pattern.e then d1452 (change pattern 8 12) else d1451 (change pattern 8 12)) = d2455 pattern
  rw [s3055, s3054]
  rfl
theorem s3057 (pattern : Twelve) : d1460 (change pattern 8 12) = d2456 pattern := by
  change (if pattern.j then d1457 (change pattern 8 12) else d1456 (change pattern 8 12)) = d2456 pattern
  rw [s3056, s3048]
  rfl
theorem s3058 (pattern : Twelve) : d1461 (change pattern 8 12) = d2457 pattern := by
  change (if pattern.j then d6 (change pattern 8 12) else d1456 (change pattern 8 12)) = d2457 pattern
  rw [s2961, s3048]
  rfl
theorem s3059 (pattern : Twelve) : d1464 (change pattern 8 12) = d2458 pattern := by
  change (if pattern.d then d1461 (change pattern 8 12) else d1460 (change pattern 8 12)) = d2458 pattern
  rw [s3058, s3057]
  rfl
theorem s3060 (pattern : Twelve) : d1466 (change pattern 8 12) = d2459 pattern := by
  change (if pattern.c then d1464 (change pattern 8 12) else d1463 (change pattern 8 12)) = d2459 pattern
  rw [s3059, s3050]
  rfl
theorem s3061 (pattern : Twelve) : d1467 (change pattern 8 12) = d2459 pattern := by
  change (if pattern.c then d1464 (change pattern 8 12) else d1456 (change pattern 8 12)) = d2459 pattern
  rw [s3059, s3048]
  rfl
theorem s3062 (pattern : Twelve) : d1469 (change pattern 8 12) = d2459 pattern := by
  change (if pattern.g then d1467 (change pattern 8 12) else d1466 (change pattern 8 12)) = d2459 pattern
  rw [s3061, s3060]
  simp only [ite_self]
theorem s3063 (pattern : Twelve) : d1470 (change pattern 8 12) = d2459 pattern := by
  change (if pattern.b then d1467 (change pattern 8 12) else d1469 (change pattern 8 12)) = d2459 pattern
  rw [s3061, s3062]
  simp only [ite_self]
theorem s3064 (pattern : Twelve) : d1277 (change pattern 8 12) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 8 12) else d15 (change pattern 8 12)) = d1277 pattern
  rw [s3010, s3025]
  rfl
theorem s3065 (pattern : Twelve) : d1331 (change pattern 8 12) = d1277 pattern := by
  change d1277 (change pattern 8 12) = d1277 pattern
  exact s3064 pattern
theorem s3066 (pattern : Twelve) : d1337 (change pattern 8 12) = d2398 pattern := by
  change (if pattern.h then d1331 (change pattern 8 12) else d1330 (change pattern 8 12)) = d2398 pattern
  rw [s3065, s3052]
  rfl
theorem s3067 (pattern : Twelve) : d1453 (change pattern 8 12) = d2460 pattern := by
  change (if pattern.f then d1337 (change pattern 8 12) else d40 (change pattern 8 12)) = d2460 pattern
  rw [s3066, s2946]
  rfl
theorem s3068 (pattern : Twelve) : d1447 (change pattern 8 12) = d2461 pattern := by
  change (if pattern.h then d128 (change pattern 8 12) else d42 (change pattern 8 12)) = d2461 pattern
  rw [s2979, s2954]
  rfl
theorem s3069 (pattern : Twelve) : d1454 (change pattern 8 12) = d2462 pattern := by
  change (if pattern.f then d6 (change pattern 8 12) else d1447 (change pattern 8 12)) = d2462 pattern
  rw [s2961, s3068]
  rfl
theorem s3070 (pattern : Twelve) : d1458 (change pattern 8 12) = d2463 pattern := by
  change (if pattern.e then d1454 (change pattern 8 12) else d1453 (change pattern 8 12)) = d2463 pattern
  rw [s3069, s3067]
  rfl
theorem s3071 (pattern : Twelve) : d1462 (change pattern 8 12) = d2464 pattern := by
  change (if pattern.j then d1458 (change pattern 8 12) else d1456 (change pattern 8 12)) = d2464 pattern
  rw [s3070, s3048]
  rfl
theorem s3072 (pattern : Twelve) : d1465 (change pattern 8 12) = d2465 pattern := by
  change (if pattern.d then d1461 (change pattern 8 12) else d1462 (change pattern 8 12)) = d2465 pattern
  rw [s3058, s3071]
  rfl
theorem s3073 (pattern : Twelve) : d1468 (change pattern 8 12) = d2466 pattern := by
  change (if pattern.c then d1465 (change pattern 8 12) else d1456 (change pattern 8 12)) = d2466 pattern
  rw [s3072, s3048]
  rfl
theorem s3074 (pattern : Twelve) : d1471 (change pattern 8 12) = d2467 pattern := by
  change (if pattern.a then d1468 (change pattern 8 12) else d1470 (change pattern 8 12)) = d2467 pattern
  rw [s3073, s3063]
  rfl
theorem s3075 (pattern : Twelve) : d1324 (change pattern 8 12) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 8 12) else d11 (change pattern 8 12)) = d1324 pattern
  rw [s2950, s2909]
  rfl
theorem s3076 (pattern : Twelve) : d1645 (change pattern 8 12) = d1324 pattern := by
  change d1324 (change pattern 8 12) = d1324 pattern
  exact s3075 pattern
theorem s3077 (pattern : Twelve) : d1716 (change pattern 8 12) = d1649 pattern := by
  change (if pattern.f then d1645 (change pattern 8 12) else d29 (change pattern 8 12)) = d1649 pattern
  rw [s3076, s2911]
  rfl
theorem s3078 (pattern : Twelve) : d1719 (change pattern 8 12) = d1656 pattern := by
  change (if pattern.e then d1452 (change pattern 8 12) else d1716 (change pattern 8 12)) = d1656 pattern
  rw [s3055, s3077]
  rfl
theorem s3079 (pattern : Twelve) : d1717 (change pattern 8 12) = d1814 pattern := by
  change (if pattern.f then d128 (change pattern 8 12) else d42 (change pattern 8 12)) = d1814 pattern
  rw [s2979, s2954]
  rfl
theorem s3080 (pattern : Twelve) : d1655 (change pattern 8 12) = d1815 pattern := by
  change (if pattern.f then d6 (change pattern 8 12) else d822 (change pattern 8 12)) = d1815 pattern
  rw [s2961, s3012]
  rfl
theorem s3081 (pattern : Twelve) : d1720 (change pattern 8 12) = d1818 pattern := by
  change (if pattern.e then d1655 (change pattern 8 12) else d1717 (change pattern 8 12)) = d1818 pattern
  rw [s3080, s3079]
  rfl
theorem s3082 (pattern : Twelve) : d1722 (change pattern 8 12) = d1992 pattern := by
  change (if pattern.j then d1720 (change pattern 8 12) else d1719 (change pattern 8 12)) = d1992 pattern
  rw [s3081, s3078]
  rfl
theorem s3083 (pattern : Twelve) : d1723 (change pattern 8 12) = d1715 pattern := by
  change (if pattern.j then d6 (change pattern 8 12) else d1719 (change pattern 8 12)) = d1715 pattern
  rw [s2961, s3078]
  rfl
theorem s3084 (pattern : Twelve) : d1725 (change pattern 8 12) = d2346 pattern := by
  change (if pattern.d then d1723 (change pattern 8 12) else d1722 (change pattern 8 12)) = d2346 pattern
  rw [s3083, s3082]
  rfl
theorem s3085 (pattern : Twelve) : d1727 (change pattern 8 12) = d2347 pattern := by
  change (if pattern.c then d1725 (change pattern 8 12) else d1719 (change pattern 8 12)) = d2347 pattern
  rw [s3084, s3078]
  rfl
theorem s3086 (pattern : Twelve) : d22 (change pattern 8 12) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 8 12) else d14 (change pattern 8 12)) = d22 pattern
  rw [s2961, s3010]
  rfl
theorem s3087 (pattern : Twelve) : d183 (change pattern 8 12) = d22 pattern := by
  change d22 (change pattern 8 12) = d22 pattern
  exact s3086 pattern
theorem s3088 (pattern : Twelve) : d1667 (change pattern 8 12) = d2410 pattern := by
  change (if pattern.h then d183 (change pattern 8 12) else d128 (change pattern 8 12)) = d2410 pattern
  rw [s3087, s2979]
  rfl
theorem s3089 (pattern : Twelve) : d1718 (change pattern 8 12) = d2468 pattern := by
  change (if pattern.f then d1667 (change pattern 8 12) else d42 (change pattern 8 12)) = d2468 pattern
  rw [s3088, s2954]
  rfl
theorem s3090 (pattern : Twelve) : d1252 (change pattern 8 12) = d2469 pattern := by
  change (if pattern.h then d6 (change pattern 8 12) else d822 (change pattern 8 12)) = d2469 pattern
  rw [s2961, s3012]
  rfl
theorem s3091 (pattern : Twelve) : d1626 (change pattern 8 12) = d2470 pattern := by
  change (if pattern.f then d6 (change pattern 8 12) else d1252 (change pattern 8 12)) = d2470 pattern
  rw [s2961, s3090]
  rfl
theorem s3092 (pattern : Twelve) : d1721 (change pattern 8 12) = d2471 pattern := by
  change (if pattern.e then d1626 (change pattern 8 12) else d1718 (change pattern 8 12)) = d2471 pattern
  rw [s3091, s3089]
  rfl
theorem s3093 (pattern : Twelve) : d1724 (change pattern 8 12) = d2472 pattern := by
  change (if pattern.j then d1721 (change pattern 8 12) else d1719 (change pattern 8 12)) = d2472 pattern
  rw [s3092, s3078]
  rfl
theorem s3094 (pattern : Twelve) : d1726 (change pattern 8 12) = d2473 pattern := by
  change (if pattern.d then d1723 (change pattern 8 12) else d1724 (change pattern 8 12)) = d2473 pattern
  rw [s3083, s3093]
  rfl
theorem s3095 (pattern : Twelve) : d1728 (change pattern 8 12) = d2474 pattern := by
  change (if pattern.c then d1726 (change pattern 8 12) else d1719 (change pattern 8 12)) = d2474 pattern
  rw [s3094, s3078]
  rfl
theorem s3096 (pattern : Twelve) : d1729 (change pattern 8 12) = d2475 pattern := by
  change (if pattern.a then d1728 (change pattern 8 12) else d1727 (change pattern 8 12)) = d2475 pattern
  rw [s3095, s3085]
  rfl
theorem s3097 (pattern : Twelve) : d0 (change pattern 8 9) = d0 pattern := by
  rfl
theorem s3098 (pattern : Twelve) : d368 (change pattern 8 9) = d0 pattern := by
  change d0 (change pattern 8 9) = d0 pattern
  exact s3097 pattern
theorem s3099 (pattern : Twelve) : d369 (change pattern 8 9) = d0 pattern := by
  change d0 (change pattern 8 9) = d0 pattern
  exact s3097 pattern
theorem s3100 (pattern : Twelve) : d375 (change pattern 8 9) = d0 pattern := by
  change (if pattern.h then d369 (change pattern 8 9) else d368 (change pattern 8 9)) = d0 pattern
  rw [s3099, s3098]
  simp only [ite_self]
theorem s3101 (pattern : Twelve) : d1 (change pattern 8 9) = d1 pattern := by
  rfl
theorem s3102 (pattern : Twelve) : d7 (change pattern 8 9) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 8 9) else d0 (change pattern 8 9)) = d7 pattern
  rw [s3101, s3097]
  rfl
theorem s3103 (pattern : Twelve) : d17 (change pattern 8 9) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 8 9) else d0 (change pattern 8 9)) = d17 pattern
  rw [s3102, s3097]
  rfl
theorem s3104 (pattern : Twelve) : d36 (change pattern 8 9) = d17 pattern := by
  change d17 (change pattern 8 9) = d17 pattern
  exact s3103 pattern
theorem s3105 (pattern : Twelve) : d376 (change pattern 8 9) = d2357 pattern := by
  change (if pattern.h then d36 (change pattern 8 9) else d369 (change pattern 8 9)) = d2357 pattern
  rw [s3104, s3099]
  rfl
theorem s3106 (pattern : Twelve) : d391 (change pattern 8 9) = d2416 pattern := by
  change (if pattern.f then d376 (change pattern 8 9) else d375 (change pattern 8 9)) = d2416 pattern
  rw [s3105, s3100]
  rfl
theorem s3107 (pattern : Twelve) : d35 (change pattern 8 9) = d0 pattern := by
  change d0 (change pattern 8 9) = d0 pattern
  exact s3097 pattern
theorem s3108 (pattern : Twelve) : d377 (change pattern 8 9) = d0 pattern := by
  change (if pattern.h then d35 (change pattern 8 9) else d369 (change pattern 8 9)) = d0 pattern
  rw [s3107, s3099]
  simp only [ite_self]
theorem s3109 (pattern : Twelve) : d2 (change pattern 8 9) = d2 pattern := by
  rfl
theorem s3110 (pattern : Twelve) : d10 (change pattern 8 9) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 8 9) else d0 (change pattern 8 9)) = d10 pattern
  rw [s3109, s3097]
  rfl
theorem s3111 (pattern : Twelve) : d3 (change pattern 8 9) = d3 pattern := by
  rfl
theorem s3112 (pattern : Twelve) : d11 (change pattern 8 9) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 8 9) else d1 (change pattern 8 9)) = d11 pattern
  rw [s3111, s3101]
  rfl
theorem s3113 (pattern : Twelve) : d19 (change pattern 8 9) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 8 9) else d10 (change pattern 8 9)) = d19 pattern
  rw [s3112, s3110]
  rfl
theorem s3114 (pattern : Twelve) : d29 (change pattern 8 9) = d19 pattern := by
  change d19 (change pattern 8 9) = d19 pattern
  exact s3113 pattern
theorem s3115 (pattern : Twelve) : d378 (change pattern 8 9) = d2358 pattern := by
  change (if pattern.h then d29 (change pattern 8 9) else d36 (change pattern 8 9)) = d2358 pattern
  rw [s3114, s3104]
  rfl
theorem s3116 (pattern : Twelve) : d392 (change pattern 8 9) = d2417 pattern := by
  change (if pattern.f then d378 (change pattern 8 9) else d377 (change pattern 8 9)) = d2417 pattern
  rw [s3115, s3108]
  rfl
theorem s3117 (pattern : Twelve) : d403 (change pattern 8 9) = d2418 pattern := by
  change (if pattern.e then d392 (change pattern 8 9) else d391 (change pattern 8 9)) = d2418 pattern
  rw [s3116, s3106]
  rfl
theorem s3118 (pattern : Twelve) : d409 (change pattern 8 9) = d2418 pattern := by
  change d403 (change pattern 8 9) = d2418 pattern
  exact s3117 pattern
theorem s3119 (pattern : Twelve) : d33 (change pattern 8 9) = d0 pattern := by
  change d0 (change pattern 8 9) = d0 pattern
  exact s3097 pattern
theorem s3120 (pattern : Twelve) : d379 (change pattern 8 9) = d0 pattern := by
  change (if pattern.h then d35 (change pattern 8 9) else d33 (change pattern 8 9)) = d0 pattern
  rw [s3107, s3119]
  simp only [ite_self]
theorem s3121 (pattern : Twelve) : d380 (change pattern 8 9) = d2357 pattern := by
  change (if pattern.h then d36 (change pattern 8 9) else d35 (change pattern 8 9)) = d2357 pattern
  rw [s3104, s3107]
  rfl
theorem s3122 (pattern : Twelve) : d393 (change pattern 8 9) = d2416 pattern := by
  change (if pattern.f then d380 (change pattern 8 9) else d379 (change pattern 8 9)) = d2416 pattern
  rw [s3121, s3120]
  rfl
theorem s3123 (pattern : Twelve) : d394 (change pattern 8 9) = d2417 pattern := by
  change (if pattern.f then d378 (change pattern 8 9) else d35 (change pattern 8 9)) = d2417 pattern
  rw [s3115, s3107]
  rfl
theorem s3124 (pattern : Twelve) : d404 (change pattern 8 9) = d2418 pattern := by
  change (if pattern.e then d394 (change pattern 8 9) else d393 (change pattern 8 9)) = d2418 pattern
  rw [s3123, s3122]
  rfl
theorem s3125 (pattern : Twelve) : d410 (change pattern 8 9) = d2418 pattern := by
  change d404 (change pattern 8 9) = d2418 pattern
  exact s3124 pattern
theorem s3126 (pattern : Twelve) : d415 (change pattern 8 9) = d2418 pattern := by
  change (if pattern.d then d410 (change pattern 8 9) else d409 (change pattern 8 9)) = d2418 pattern
  rw [s3125, s3118]
  simp only [ite_self]
theorem s3127 (pattern : Twelve) : d39 (change pattern 8 9) = d2 pattern := by
  change d2 (change pattern 8 9) = d2 pattern
  exact s3109 pattern
theorem s3128 (pattern : Twelve) : d9 (change pattern 8 9) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 8 9) else d2 (change pattern 8 9)) = d9 pattern
  rw [s3111, s3109]
  rfl
theorem s3129 (pattern : Twelve) : d23 (change pattern 8 9) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 8 9) else d2 (change pattern 8 9)) = d23 pattern
  rw [s3128, s3109]
  rfl
theorem s3130 (pattern : Twelve) : d40 (change pattern 8 9) = d23 pattern := by
  change d23 (change pattern 8 9) = d23 pattern
  exact s3129 pattern
theorem s3131 (pattern : Twelve) : d384 (change pattern 8 9) = d2360 pattern := by
  change (if pattern.h then d40 (change pattern 8 9) else d39 (change pattern 8 9)) = d2360 pattern
  rw [s3130, s3127]
  rfl
theorem s3132 (pattern : Twelve) : d397 (change pattern 8 9) = d2419 pattern := by
  change (if pattern.f then d384 (change pattern 8 9) else d39 (change pattern 8 9)) = d2419 pattern
  rw [s3131, s3127]
  rfl
theorem s3133 (pattern : Twelve) : d4 (change pattern 8 9) = d4 pattern := by
  rfl
theorem s3134 (pattern : Twelve) : d16 (change pattern 8 9) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 8 9) else d2 (change pattern 8 9)) = d16 pattern
  rw [s3133, s3109]
  rfl
theorem s3135 (pattern : Twelve) : d5 (change pattern 8 9) = d5 pattern := by
  rfl
theorem s3136 (pattern : Twelve) : d12 (change pattern 8 9) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 8 9) else d3 (change pattern 8 9)) = d12 pattern
  rw [s3135, s3111]
  rfl
theorem s3137 (pattern : Twelve) : d25 (change pattern 8 9) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 8 9) else d16 (change pattern 8 9)) = d25 pattern
  rw [s3136, s3134]
  rfl
theorem s3138 (pattern : Twelve) : d42 (change pattern 8 9) = d25 pattern := by
  change d25 (change pattern 8 9) = d25 pattern
  exact s3137 pattern
theorem s3139 (pattern : Twelve) : d385 (change pattern 8 9) = d2361 pattern := by
  change (if pattern.h then d42 (change pattern 8 9) else d40 (change pattern 8 9)) = d2361 pattern
  rw [s3138, s3130]
  rfl
theorem s3140 (pattern : Twelve) : d398 (change pattern 8 9) = d2420 pattern := by
  change (if pattern.f then d385 (change pattern 8 9) else d39 (change pattern 8 9)) = d2420 pattern
  rw [s3139, s3127]
  rfl
theorem s3141 (pattern : Twelve) : d406 (change pattern 8 9) = d2421 pattern := by
  change (if pattern.e then d398 (change pattern 8 9) else d397 (change pattern 8 9)) = d2421 pattern
  rw [s3140, s3132]
  rfl
theorem s3142 (pattern : Twelve) : d411 (change pattern 8 9) = d2421 pattern := by
  change d406 (change pattern 8 9) = d2421 pattern
  exact s3141 pattern
theorem s3143 (pattern : Twelve) : d6 (change pattern 8 9) = d6 pattern := by
  rfl
theorem s3144 (pattern : Twelve) : d412 (change pattern 8 9) = d6 pattern := by
  change d6 (change pattern 8 9) = d6 pattern
  exact s3143 pattern
theorem s3145 (pattern : Twelve) : d416 (change pattern 8 9) = d2476 pattern := by
  change (if pattern.d then d412 (change pattern 8 9) else d411 (change pattern 8 9)) = d2476 pattern
  rw [s3144, s3142]
  rfl
theorem s3146 (pattern : Twelve) : d419 (change pattern 8 9) = d2477 pattern := by
  change (if pattern.c then d416 (change pattern 8 9) else d415 (change pattern 8 9)) = d2477 pattern
  rw [s3145, s3126]
  rfl
theorem s3147 (pattern : Twelve) : d399 (change pattern 8 9) = d2416 pattern := by
  change (if pattern.f then d380 (change pattern 8 9) else d35 (change pattern 8 9)) = d2416 pattern
  rw [s3121, s3107]
  rfl
theorem s3148 (pattern : Twelve) : d407 (change pattern 8 9) = d2418 pattern := by
  change (if pattern.e then d394 (change pattern 8 9) else d399 (change pattern 8 9)) = d2418 pattern
  rw [s3123, s3147]
  rfl
theorem s3149 (pattern : Twelve) : d413 (change pattern 8 9) = d2421 pattern := by
  change d406 (change pattern 8 9) = d2421 pattern
  exact s3141 pattern
end NetHack.Sokoban21.Diagram
