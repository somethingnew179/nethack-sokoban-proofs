/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions21
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s3300 (pattern : Twelve) : d436 (change pattern 5 4) = d59 pattern := by
  change d59 (change pattern 5 4) = d59 pattern
  exact s3299 pattern
theorem s3301 (pattern : Twelve) : d449 (change pattern 5 4) = d59 pattern := by
  change d436 (change pattern 5 4) = d59 pattern
  exact s3300 pattern
theorem s3302 (pattern : Twelve) : d457 (change pattern 5 4) = d2500 pattern := by
  change (if pattern.j then d449 (change pattern 5 4) else d448 (change pattern 5 4)) = d2500 pattern
  rw [s3301, s3295]
  rfl
theorem s3303 (pattern : Twelve) : d450 (change pattern 5 4) = d56 pattern := by
  change d432 (change pattern 5 4) = d56 pattern
  exact s3290 pattern
theorem s3304 (pattern : Twelve) : d458 (change pattern 5 4) = d2501 pattern := by
  change (if pattern.j then d6 (change pattern 5 4) else d450 (change pattern 5 4)) = d2501 pattern
  rw [s3278, s3303]
  rfl
theorem s3305 (pattern : Twelve) : d466 (change pattern 5 4) = d2502 pattern := by
  change (if pattern.d then d458 (change pattern 5 4) else d457 (change pattern 5 4)) = d2502 pattern
  rw [s3304, s3302]
  rfl
theorem s3306 (pattern : Twelve) : d471 (change pattern 5 4) = d2503 pattern := by
  change (if pattern.c then d466 (change pattern 5 4) else d465 (change pattern 5 4)) = d2503 pattern
  rw [s3305, s3293]
  rfl
theorem s3307 (pattern : Twelve) : d438 (change pattern 5 4) = d0 pattern := by
  change d0 (change pattern 5 4) = d0 pattern
  exact s3272 pattern
theorem s3308 (pattern : Twelve) : d440 (change pattern 5 4) = d54 pattern := by
  change d54 (change pattern 5 4) = d54 pattern
  exact s3282 pattern
theorem s3309 (pattern : Twelve) : d451 (change pattern 5 4) = d54 pattern := by
  change d440 (change pattern 5 4) = d54 pattern
  exact s3308 pattern
theorem s3310 (pattern : Twelve) : d459 (change pattern 5 4) = d2497 pattern := by
  change (if pattern.j then d451 (change pattern 5 4) else d438 (change pattern 5 4)) = d2497 pattern
  rw [s3309, s3307]
  rfl
theorem s3311 (pattern : Twelve) : d460 (change pattern 5 4) = d2498 pattern := by
  change (if pattern.j then d432 (change pattern 5 4) else d438 (change pattern 5 4)) = d2498 pattern
  rw [s3290, s3307]
  rfl
theorem s3312 (pattern : Twelve) : d467 (change pattern 5 4) = d2499 pattern := by
  change (if pattern.d then d460 (change pattern 5 4) else d459 (change pattern 5 4)) = d2499 pattern
  rw [s3311, s3310]
  rfl
theorem s3313 (pattern : Twelve) : d441 (change pattern 5 4) = d30 pattern := by
  change d30 (change pattern 5 4) = d30 pattern
  exact s3276 pattern
theorem s3314 (pattern : Twelve) : d461 (change pattern 5 4) = d2500 pattern := by
  change (if pattern.j then d436 (change pattern 5 4) else d441 (change pattern 5 4)) = d2500 pattern
  rw [s3300, s3313]
  rfl
theorem s3315 (pattern : Twelve) : d462 (change pattern 5 4) = d2501 pattern := by
  change (if pattern.j then d6 (change pattern 5 4) else d432 (change pattern 5 4)) = d2501 pattern
  rw [s3278, s3290]
  rfl
theorem s3316 (pattern : Twelve) : d468 (change pattern 5 4) = d2502 pattern := by
  change (if pattern.d then d462 (change pattern 5 4) else d461 (change pattern 5 4)) = d2502 pattern
  rw [s3315, s3314]
  rfl
theorem s3317 (pattern : Twelve) : d472 (change pattern 5 4) = d2503 pattern := by
  change (if pattern.c then d468 (change pattern 5 4) else d467 (change pattern 5 4)) = d2503 pattern
  rw [s3316, s3312]
  rfl
theorem s3318 (pattern : Twelve) : d474 (change pattern 5 4) = d2503 pattern := by
  change (if pattern.g then d472 (change pattern 5 4) else d471 (change pattern 5 4)) = d2503 pattern
  rw [s3317, s3306]
  simp only [ite_self]
theorem s3319 (pattern : Twelve) : d475 (change pattern 5 4) = d2503 pattern := by
  change (if pattern.b then d472 (change pattern 5 4) else d474 (change pattern 5 4)) = d2503 pattern
  rw [s3317, s3318]
  simp only [ite_self]
theorem s3320 (pattern : Twelve) : d452 (change pattern 5 4) = d56 pattern := by
  change d432 (change pattern 5 4) = d56 pattern
  exact s3290 pattern
theorem s3321 (pattern : Twelve) : d463 (change pattern 5 4) = d2498 pattern := by
  change (if pattern.j then d452 (change pattern 5 4) else d438 (change pattern 5 4)) = d2498 pattern
  rw [s3320, s3307]
  rfl
theorem s3322 (pattern : Twelve) : d469 (change pattern 5 4) = d2498 pattern := by
  change (if pattern.d then d460 (change pattern 5 4) else d463 (change pattern 5 4)) = d2498 pattern
  rw [s3311, s3321]
  simp only [ite_self]
theorem s3323 (pattern : Twelve) : d3 (change pattern 5 4) = d3 pattern := by
  rfl
theorem s3324 (pattern : Twelve) : d123 (change pattern 5 4) = d123 pattern := by
  change (if pattern.i then d3 (change pattern 5 4) else d0 (change pattern 5 4)) = d123 pattern
  rw [s3323, s3272]
  rfl
theorem s3325 (pattern : Twelve) : d132 (change pattern 5 4) = d132 pattern := by
  change (if pattern.h then d123 (change pattern 5 4) else d30 (change pattern 5 4)) = d132 pattern
  rw [s3324, s3276]
  rfl
theorem s3326 (pattern : Twelve) : d442 (change pattern 5 4) = d132 pattern := by
  change d132 (change pattern 5 4) = d132 pattern
  exact s3325 pattern
theorem s3327 (pattern : Twelve) : d453 (change pattern 5 4) = d132 pattern := by
  change d442 (change pattern 5 4) = d132 pattern
  exact s3326 pattern
theorem s3328 (pattern : Twelve) : d126 (change pattern 5 4) = d126 pattern := by
  change (if pattern.i then d5 (change pattern 5 4) else d2 (change pattern 5 4)) = d126 pattern
  rw [s3277, s3275]
  rfl
theorem s3329 (pattern : Twelve) : d47 (change pattern 5 4) = d47 pattern := by
  change (if pattern.i then d6 (change pattern 5 4) else d3 (change pattern 5 4)) = d47 pattern
  rw [s3278, s3323]
  rfl
theorem s3330 (pattern : Twelve) : d134 (change pattern 5 4) = d134 pattern := by
  change (if pattern.h then d47 (change pattern 5 4) else d126 (change pattern 5 4)) = d134 pattern
  rw [s3329, s3328]
  rfl
theorem s3331 (pattern : Twelve) : d443 (change pattern 5 4) = d134 pattern := by
  change d134 (change pattern 5 4) = d134 pattern
  exact s3330 pattern
theorem s3332 (pattern : Twelve) : d454 (change pattern 5 4) = d134 pattern := by
  change d443 (change pattern 5 4) = d134 pattern
  exact s3331 pattern
theorem s3333 (pattern : Twelve) : d464 (change pattern 5 4) = d2504 pattern := by
  change (if pattern.j then d454 (change pattern 5 4) else d453 (change pattern 5 4)) = d2504 pattern
  rw [s3332, s3327]
  rfl
theorem s3334 (pattern : Twelve) : d470 (change pattern 5 4) = d2505 pattern := by
  change (if pattern.d then d462 (change pattern 5 4) else d464 (change pattern 5 4)) = d2505 pattern
  rw [s3315, s3333]
  rfl
theorem s3335 (pattern : Twelve) : d473 (change pattern 5 4) = d2506 pattern := by
  change (if pattern.c then d470 (change pattern 5 4) else d469 (change pattern 5 4)) = d2506 pattern
  rw [s3334, s3322]
  rfl
theorem s3336 (pattern : Twelve) : d476 (change pattern 5 4) = d2507 pattern := by
  change (if pattern.a then d473 (change pattern 5 4) else d475 (change pattern 5 4)) = d2507 pattern
  rw [s3335, s3319]
  rfl
theorem s3337 (pattern : Twelve) : d1 (change pattern 5 4) = d1 pattern := by
  rfl
theorem s3338 (pattern : Twelve) : d7 (change pattern 5 4) = d7 pattern := by
  change (if pattern.l then d1 (change pattern 5 4) else d0 (change pattern 5 4)) = d7 pattern
  rw [s3337, s3272]
  rfl
theorem s3339 (pattern : Twelve) : d17 (change pattern 5 4) = d17 pattern := by
  change (if pattern.k then d7 (change pattern 5 4) else d0 (change pattern 5 4)) = d17 pattern
  rw [s3338, s3272]
  rfl
theorem s3340 (pattern : Twelve) : d1070 (change pattern 5 4) = d17 pattern := by
  change d17 (change pattern 5 4) = d17 pattern
  exact s3339 pattern
theorem s3341 (pattern : Twelve) : d1078 (change pattern 5 4) = d17 pattern := by
  change d1070 (change pattern 5 4) = d17 pattern
  exact s3340 pattern
theorem s3342 (pattern : Twelve) : d9 (change pattern 5 4) = d9 pattern := by
  change (if pattern.l then d3 (change pattern 5 4) else d2 (change pattern 5 4)) = d9 pattern
  rw [s3323, s3275]
  rfl
theorem s3343 (pattern : Twelve) : d23 (change pattern 5 4) = d23 pattern := by
  change (if pattern.k then d9 (change pattern 5 4) else d2 (change pattern 5 4)) = d23 pattern
  rw [s3342, s3275]
  rfl
theorem s3344 (pattern : Twelve) : d34 (change pattern 5 4) = d34 pattern := by
  change (if pattern.i then d23 (change pattern 5 4) else d17 (change pattern 5 4)) = d34 pattern
  rw [s3343, s3339]
  rfl
theorem s3345 (pattern : Twelve) : d36 (change pattern 5 4) = d36 pattern := by
  change (if pattern.i then d6 (change pattern 5 4) else d17 (change pattern 5 4)) = d36 pattern
  rw [s3278, s3339]
  rfl
theorem s3346 (pattern : Twelve) : d827 (change pattern 5 4) = d827 pattern := by
  change (if pattern.h then d36 (change pattern 5 4) else d34 (change pattern 5 4)) = d827 pattern
  rw [s3345, s3344]
  rfl
theorem s3347 (pattern : Twelve) : d1072 (change pattern 5 4) = d827 pattern := by
  change d827 (change pattern 5 4) = d827 pattern
  exact s3346 pattern
theorem s3348 (pattern : Twelve) : d1079 (change pattern 5 4) = d827 pattern := by
  change d1072 (change pattern 5 4) = d827 pattern
  exact s3347 pattern
theorem s3349 (pattern : Twelve) : d1088 (change pattern 5 4) = d2508 pattern := by
  change (if pattern.j then d1079 (change pattern 5 4) else d1078 (change pattern 5 4)) = d2508 pattern
  rw [s3348, s3341]
  rfl
theorem s3350 (pattern : Twelve) : d1073 (change pattern 5 4) = d17 pattern := by
  change d17 (change pattern 5 4) = d17 pattern
  exact s3339 pattern
theorem s3351 (pattern : Twelve) : d1080 (change pattern 5 4) = d17 pattern := by
  change d1073 (change pattern 5 4) = d17 pattern
  exact s3350 pattern
theorem s3352 (pattern : Twelve) : d1081 (change pattern 5 4) = d827 pattern := by
  change d1072 (change pattern 5 4) = d827 pattern
  exact s3347 pattern
theorem s3353 (pattern : Twelve) : d1089 (change pattern 5 4) = d2508 pattern := by
  change (if pattern.j then d1081 (change pattern 5 4) else d1080 (change pattern 5 4)) = d2508 pattern
  rw [s3352, s3351]
  rfl
theorem s3354 (pattern : Twelve) : d1095 (change pattern 5 4) = d2508 pattern := by
  change (if pattern.d then d1089 (change pattern 5 4) else d1088 (change pattern 5 4)) = d2508 pattern
  rw [s3353, s3349]
  simp only [ite_self]
theorem s3355 (pattern : Twelve) : d1074 (change pattern 5 4) = d34 pattern := by
  change d34 (change pattern 5 4) = d34 pattern
  exact s3344 pattern
theorem s3356 (pattern : Twelve) : d1082 (change pattern 5 4) = d34 pattern := by
  change d1074 (change pattern 5 4) = d34 pattern
  exact s3355 pattern
theorem s3357 (pattern : Twelve) : d15 (change pattern 5 4) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 5 4) else d4 (change pattern 5 4)) = d15 pattern
  rw [s3277, s3296]
  rfl
theorem s3358 (pattern : Twelve) : d24 (change pattern 5 4) = d24 pattern := by
  change (if pattern.k then d15 (change pattern 5 4) else d4 (change pattern 5 4)) = d24 pattern
  rw [s3357, s3296]
  rfl
theorem s3359 (pattern : Twelve) : d41 (change pattern 5 4) = d41 pattern := by
  change (if pattern.i then d24 (change pattern 5 4) else d23 (change pattern 5 4)) = d41 pattern
  rw [s3358, s3343]
  rfl
theorem s3360 (pattern : Twelve) : d40 (change pattern 5 4) = d40 pattern := by
  change (if pattern.i then d6 (change pattern 5 4) else d23 (change pattern 5 4)) = d40 pattern
  rw [s3278, s3343]
  rfl
theorem s3361 (pattern : Twelve) : d830 (change pattern 5 4) = d830 pattern := by
  change (if pattern.h then d40 (change pattern 5 4) else d41 (change pattern 5 4)) = d830 pattern
  rw [s3360, s3359]
  rfl
theorem s3362 (pattern : Twelve) : d1075 (change pattern 5 4) = d830 pattern := by
  change d830 (change pattern 5 4) = d830 pattern
  exact s3361 pattern
theorem s3363 (pattern : Twelve) : d1083 (change pattern 5 4) = d830 pattern := by
  change d1075 (change pattern 5 4) = d830 pattern
  exact s3362 pattern
theorem s3364 (pattern : Twelve) : d1090 (change pattern 5 4) = d2509 pattern := by
  change (if pattern.j then d1083 (change pattern 5 4) else d1082 (change pattern 5 4)) = d2509 pattern
  rw [s3363, s3356]
  rfl
theorem s3365 (pattern : Twelve) : d1091 (change pattern 5 4) = d2510 pattern := by
  change (if pattern.j then d6 (change pattern 5 4) else d1081 (change pattern 5 4)) = d2510 pattern
  rw [s3278, s3352]
  rfl
theorem s3366 (pattern : Twelve) : d1096 (change pattern 5 4) = d2511 pattern := by
  change (if pattern.d then d1091 (change pattern 5 4) else d1090 (change pattern 5 4)) = d2511 pattern
  rw [s3365, s3364]
  rfl
theorem s3367 (pattern : Twelve) : d1099 (change pattern 5 4) = d2512 pattern := by
  change (if pattern.c then d1096 (change pattern 5 4) else d1095 (change pattern 5 4)) = d2512 pattern
  rw [s3366, s3354]
  rfl
theorem s3368 (pattern : Twelve) : d1084 (change pattern 5 4) = d17 pattern := by
  change d1073 (change pattern 5 4) = d17 pattern
  exact s3350 pattern
theorem s3369 (pattern : Twelve) : d1092 (change pattern 5 4) = d2508 pattern := by
  change (if pattern.j then d1081 (change pattern 5 4) else d1084 (change pattern 5 4)) = d2508 pattern
  rw [s3352, s3368]
  rfl
theorem s3370 (pattern : Twelve) : d1085 (change pattern 5 4) = d34 pattern := by
  change d1074 (change pattern 5 4) = d34 pattern
  exact s3355 pattern
theorem s3371 (pattern : Twelve) : d1093 (change pattern 5 4) = d2509 pattern := by
  change (if pattern.j then d1083 (change pattern 5 4) else d1085 (change pattern 5 4)) = d2509 pattern
  rw [s3363, s3370]
  rfl
theorem s3372 (pattern : Twelve) : d1097 (change pattern 5 4) = d2511 pattern := by
  change (if pattern.d then d1091 (change pattern 5 4) else d1093 (change pattern 5 4)) = d2511 pattern
  rw [s3365, s3371]
  rfl
theorem s3373 (pattern : Twelve) : d1100 (change pattern 5 4) = d2512 pattern := by
  change (if pattern.c then d1097 (change pattern 5 4) else d1092 (change pattern 5 4)) = d2512 pattern
  rw [s3372, s3369]
  rfl
theorem s3374 (pattern : Twelve) : d1102 (change pattern 5 4) = d2512 pattern := by
  change (if pattern.g then d1100 (change pattern 5 4) else d1099 (change pattern 5 4)) = d2512 pattern
  rw [s3373, s3367]
  simp only [ite_self]
theorem s3375 (pattern : Twelve) : d1103 (change pattern 5 4) = d2512 pattern := by
  change (if pattern.b then d1100 (change pattern 5 4) else d1102 (change pattern 5 4)) = d2512 pattern
  rw [s3373, s3374]
  simp only [ite_self]
theorem s3376 (pattern : Twelve) : d117 (change pattern 5 4) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 5 4) else d3 (change pattern 5 4)) = d117 pattern
  rw [s3296, s3323]
  rfl
theorem s3377 (pattern : Twelve) : d119 (change pattern 5 4) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 5 4) else d3 (change pattern 5 4)) = d119 pattern
  rw [s3376, s3323]
  rfl
theorem s3378 (pattern : Twelve) : d879 (change pattern 5 4) = d879 pattern := by
  change (if pattern.i then d119 (change pattern 5 4) else d17 (change pattern 5 4)) = d879 pattern
  rw [s3377, s3339]
  rfl
theorem s3379 (pattern : Twelve) : d886 (change pattern 5 4) = d886 pattern := by
  change (if pattern.h then d879 (change pattern 5 4) else d34 (change pattern 5 4)) = d886 pattern
  rw [s3378, s3344]
  rfl
theorem s3380 (pattern : Twelve) : d1076 (change pattern 5 4) = d886 pattern := by
  change d886 (change pattern 5 4) = d886 pattern
  exact s3379 pattern
theorem s3381 (pattern : Twelve) : d1086 (change pattern 5 4) = d886 pattern := by
  change d1076 (change pattern 5 4) = d886 pattern
  exact s3380 pattern
theorem s3382 (pattern : Twelve) : d118 (change pattern 5 4) = d118 pattern := by
  change (if pattern.k then d14 (change pattern 5 4) else d5 (change pattern 5 4)) = d118 pattern
  rw [s3279, s3277]
  rfl
theorem s3383 (pattern : Twelve) : d881 (change pattern 5 4) = d881 pattern := by
  change (if pattern.i then d118 (change pattern 5 4) else d23 (change pattern 5 4)) = d881 pattern
  rw [s3382, s3343]
  rfl
theorem s3384 (pattern : Twelve) : d125 (change pattern 5 4) = d125 pattern := by
  change (if pattern.i then d6 (change pattern 5 4) else d119 (change pattern 5 4)) = d125 pattern
  rw [s3278, s3377]
  rfl
theorem s3385 (pattern : Twelve) : d888 (change pattern 5 4) = d888 pattern := by
  change (if pattern.h then d125 (change pattern 5 4) else d881 (change pattern 5 4)) = d888 pattern
  rw [s3384, s3383]
  rfl
theorem s3386 (pattern : Twelve) : d1077 (change pattern 5 4) = d888 pattern := by
  change d888 (change pattern 5 4) = d888 pattern
  exact s3385 pattern
theorem s3387 (pattern : Twelve) : d1087 (change pattern 5 4) = d888 pattern := by
  change d1077 (change pattern 5 4) = d888 pattern
  exact s3386 pattern
theorem s3388 (pattern : Twelve) : d1094 (change pattern 5 4) = d2513 pattern := by
  change (if pattern.j then d1087 (change pattern 5 4) else d1086 (change pattern 5 4)) = d2513 pattern
  rw [s3387, s3381]
  rfl
theorem s3389 (pattern : Twelve) : d1098 (change pattern 5 4) = d2514 pattern := by
  change (if pattern.d then d1091 (change pattern 5 4) else d1094 (change pattern 5 4)) = d2514 pattern
  rw [s3365, s3388]
  rfl
theorem s3390 (pattern : Twelve) : d1101 (change pattern 5 4) = d2515 pattern := by
  change (if pattern.c then d1098 (change pattern 5 4) else d1092 (change pattern 5 4)) = d2515 pattern
  rw [s3389, s3369]
  rfl
theorem s3391 (pattern : Twelve) : d1104 (change pattern 5 4) = d2516 pattern := by
  change (if pattern.a then d1101 (change pattern 5 4) else d1103 (change pattern 5 4)) = d2516 pattern
  rw [s3390, s3375]
  rfl
theorem s3392 (pattern : Twelve) : d10 (change pattern 5 4) = d10 pattern := by
  change (if pattern.l then d2 (change pattern 5 4) else d0 (change pattern 5 4)) = d10 pattern
  rw [s3275, s3272]
  rfl
theorem s3393 (pattern : Twelve) : d11 (change pattern 5 4) = d11 pattern := by
  change (if pattern.l then d3 (change pattern 5 4) else d1 (change pattern 5 4)) = d11 pattern
  rw [s3323, s3337]
  rfl
theorem s3394 (pattern : Twelve) : d19 (change pattern 5 4) = d19 pattern := by
  change (if pattern.k then d11 (change pattern 5 4) else d10 (change pattern 5 4)) = d19 pattern
  rw [s3393, s3392]
  rfl
theorem s3395 (pattern : Twelve) : d1294 (change pattern 5 4) = d19 pattern := by
  change d19 (change pattern 5 4) = d19 pattern
  exact s3394 pattern
theorem s3396 (pattern : Twelve) : d1472 (change pattern 5 4) = d19 pattern := by
  change d1294 (change pattern 5 4) = d19 pattern
  exact s3395 pattern
theorem s3397 (pattern : Twelve) : d16 (change pattern 5 4) = d16 pattern := by
  change (if pattern.l then d4 (change pattern 5 4) else d2 (change pattern 5 4)) = d16 pattern
  rw [s3296, s3275]
  rfl
theorem s3398 (pattern : Twelve) : d12 (change pattern 5 4) = d12 pattern := by
  change (if pattern.l then d5 (change pattern 5 4) else d3 (change pattern 5 4)) = d12 pattern
  rw [s3277, s3323]
  rfl
theorem s3399 (pattern : Twelve) : d25 (change pattern 5 4) = d25 pattern := by
  change (if pattern.k then d12 (change pattern 5 4) else d16 (change pattern 5 4)) = d25 pattern
  rw [s3398, s3397]
  rfl
theorem s3400 (pattern : Twelve) : d817 (change pattern 5 4) = d817 pattern := by
  change (if pattern.i then d25 (change pattern 5 4) else d19 (change pattern 5 4)) = d817 pattern
  rw [s3399, s3394]
  rfl
theorem s3401 (pattern : Twelve) : d29 (change pattern 5 4) = d29 pattern := by
  change (if pattern.i then d6 (change pattern 5 4) else d19 (change pattern 5 4)) = d29 pattern
  rw [s3278, s3394]
  rfl
theorem s3402 (pattern : Twelve) : d1286 (change pattern 5 4) = d1286 pattern := by
  change (if pattern.h then d29 (change pattern 5 4) else d817 (change pattern 5 4)) = d1286 pattern
  rw [s3401, s3400]
  rfl
theorem s3403 (pattern : Twelve) : d1296 (change pattern 5 4) = d1286 pattern := by
  change d1286 (change pattern 5 4) = d1286 pattern
  exact s3402 pattern
theorem s3404 (pattern : Twelve) : d1473 (change pattern 5 4) = d1286 pattern := by
  change d1296 (change pattern 5 4) = d1286 pattern
  exact s3403 pattern
theorem s3405 (pattern : Twelve) : d1479 (change pattern 5 4) = d2517 pattern := by
  change (if pattern.j then d1473 (change pattern 5 4) else d1472 (change pattern 5 4)) = d2517 pattern
  rw [s3404, s3396]
  rfl
theorem s3406 (pattern : Twelve) : d1474 (change pattern 5 4) = d19 pattern := by
  change d1294 (change pattern 5 4) = d19 pattern
  exact s3395 pattern
theorem s3407 (pattern : Twelve) : d1480 (change pattern 5 4) = d2517 pattern := by
  change (if pattern.j then d1473 (change pattern 5 4) else d1474 (change pattern 5 4)) = d2517 pattern
  rw [s3404, s3406]
  rfl
theorem s3408 (pattern : Twelve) : d1484 (change pattern 5 4) = d2517 pattern := by
  change (if pattern.d then d1480 (change pattern 5 4) else d1479 (change pattern 5 4)) = d2517 pattern
  rw [s3407, s3405]
  simp only [ite_self]
theorem s3409 (pattern : Twelve) : d1298 (change pattern 5 4) = d817 pattern := by
  change d817 (change pattern 5 4) = d817 pattern
  exact s3400 pattern
theorem s3410 (pattern : Twelve) : d1475 (change pattern 5 4) = d817 pattern := by
  change d1298 (change pattern 5 4) = d817 pattern
  exact s3409 pattern
theorem s3411 (pattern : Twelve) : d13 (change pattern 5 4) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 5 4) else d4 (change pattern 5 4)) = d13 pattern
  rw [s3278, s3296]
  rfl
theorem s3412 (pattern : Twelve) : d21 (change pattern 5 4) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 5 4) else d13 (change pattern 5 4)) = d21 pattern
  rw [s3279, s3411]
  rfl
theorem s3413 (pattern : Twelve) : d821 (change pattern 5 4) = d821 pattern := by
  change (if pattern.i then d21 (change pattern 5 4) else d25 (change pattern 5 4)) = d821 pattern
  rw [s3412, s3399]
  rfl
theorem s3414 (pattern : Twelve) : d42 (change pattern 5 4) = d42 pattern := by
  change (if pattern.i then d6 (change pattern 5 4) else d25 (change pattern 5 4)) = d42 pattern
  rw [s3278, s3399]
  rfl
theorem s3415 (pattern : Twelve) : d1289 (change pattern 5 4) = d1289 pattern := by
  change (if pattern.h then d42 (change pattern 5 4) else d821 (change pattern 5 4)) = d1289 pattern
  rw [s3414, s3413]
  rfl
theorem s3416 (pattern : Twelve) : d1300 (change pattern 5 4) = d1289 pattern := by
  change d1289 (change pattern 5 4) = d1289 pattern
  exact s3415 pattern
theorem s3417 (pattern : Twelve) : d1476 (change pattern 5 4) = d1289 pattern := by
  change d1300 (change pattern 5 4) = d1289 pattern
  exact s3416 pattern
theorem s3418 (pattern : Twelve) : d1481 (change pattern 5 4) = d2518 pattern := by
  change (if pattern.j then d1476 (change pattern 5 4) else d1475 (change pattern 5 4)) = d2518 pattern
  rw [s3417, s3410]
  rfl
theorem s3419 (pattern : Twelve) : d1482 (change pattern 5 4) = d2519 pattern := by
  change (if pattern.j then d6 (change pattern 5 4) else d1473 (change pattern 5 4)) = d2519 pattern
  rw [s3278, s3404]
  rfl
theorem s3420 (pattern : Twelve) : d1485 (change pattern 5 4) = d2520 pattern := by
  change (if pattern.d then d1482 (change pattern 5 4) else d1481 (change pattern 5 4)) = d2520 pattern
  rw [s3419, s3418]
  rfl
theorem s3421 (pattern : Twelve) : d1487 (change pattern 5 4) = d2521 pattern := by
  change (if pattern.c then d1485 (change pattern 5 4) else d1484 (change pattern 5 4)) = d2521 pattern
  rw [s3420, s3408]
  rfl
theorem s3422 (pattern : Twelve) : d1488 (change pattern 5 4) = d2521 pattern := by
  change (if pattern.c then d1485 (change pattern 5 4) else d1480 (change pattern 5 4)) = d2521 pattern
  rw [s3420, s3407]
  rfl
theorem s3423 (pattern : Twelve) : d1490 (change pattern 5 4) = d2521 pattern := by
  change (if pattern.g then d1488 (change pattern 5 4) else d1487 (change pattern 5 4)) = d2521 pattern
  rw [s3422, s3421]
  simp only [ite_self]
theorem s3424 (pattern : Twelve) : d1491 (change pattern 5 4) = d2521 pattern := by
  change (if pattern.b then d1488 (change pattern 5 4) else d1490 (change pattern 5 4)) = d2521 pattern
  rw [s3422, s3423]
  simp only [ite_self]
theorem s3425 (pattern : Twelve) : d20 (change pattern 5 4) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 5 4) else d12 (change pattern 5 4)) = d20 pattern
  rw [s3411, s3398]
  rfl
theorem s3426 (pattern : Twelve) : d1329 (change pattern 5 4) = d1329 pattern := by
  change (if pattern.i then d20 (change pattern 5 4) else d19 (change pattern 5 4)) = d1329 pattern
  rw [s3425, s3394]
  rfl
theorem s3427 (pattern : Twelve) : d1336 (change pattern 5 4) = d1336 pattern := by
  change (if pattern.h then d1329 (change pattern 5 4) else d817 (change pattern 5 4)) = d1336 pattern
  rw [s3426, s3400]
  rfl
theorem s3428 (pattern : Twelve) : d1342 (change pattern 5 4) = d1336 pattern := by
  change d1336 (change pattern 5 4) = d1336 pattern
  exact s3427 pattern
theorem s3429 (pattern : Twelve) : d1477 (change pattern 5 4) = d1336 pattern := by
  change d1342 (change pattern 5 4) = d1336 pattern
  exact s3428 pattern
theorem s3430 (pattern : Twelve) : d1332 (change pattern 5 4) = d1332 pattern := by
  change (if pattern.i then d22 (change pattern 5 4) else d25 (change pattern 5 4)) = d1332 pattern
  rw [s3280, s3399]
  rfl
theorem s3431 (pattern : Twelve) : d128 (change pattern 5 4) = d128 pattern := by
  change (if pattern.i then d6 (change pattern 5 4) else d20 (change pattern 5 4)) = d128 pattern
  rw [s3278, s3425]
  rfl
theorem s3432 (pattern : Twelve) : d1338 (change pattern 5 4) = d1338 pattern := by
  change (if pattern.h then d128 (change pattern 5 4) else d1332 (change pattern 5 4)) = d1338 pattern
  rw [s3431, s3430]
  rfl
theorem s3433 (pattern : Twelve) : d1344 (change pattern 5 4) = d1338 pattern := by
  change d1338 (change pattern 5 4) = d1338 pattern
  exact s3432 pattern
theorem s3434 (pattern : Twelve) : d1478 (change pattern 5 4) = d1338 pattern := by
  change d1344 (change pattern 5 4) = d1338 pattern
  exact s3433 pattern
theorem s3435 (pattern : Twelve) : d1483 (change pattern 5 4) = d2522 pattern := by
  change (if pattern.j then d1478 (change pattern 5 4) else d1477 (change pattern 5 4)) = d2522 pattern
  rw [s3434, s3429]
  rfl
theorem s3436 (pattern : Twelve) : d1486 (change pattern 5 4) = d2523 pattern := by
  change (if pattern.d then d1482 (change pattern 5 4) else d1483 (change pattern 5 4)) = d2523 pattern
  rw [s3419, s3435]
  rfl
theorem s3437 (pattern : Twelve) : d1489 (change pattern 5 4) = d2524 pattern := by
  change (if pattern.c then d1486 (change pattern 5 4) else d1480 (change pattern 5 4)) = d2524 pattern
  rw [s3436, s3407]
  rfl
theorem s3438 (pattern : Twelve) : d1492 (change pattern 5 4) = d2525 pattern := by
  change (if pattern.a then d1489 (change pattern 5 4) else d1491 (change pattern 5 4)) = d2525 pattern
  rw [s3437, s3424]
  rfl
theorem s3439 (pattern : Twelve) : d1650 (change pattern 5 4) = d25 pattern := by
  change d25 (change pattern 5 4) = d25 pattern
  exact s3399 pattern
theorem s3440 (pattern : Twelve) : d1730 (change pattern 5 4) = d25 pattern := by
  change d1650 (change pattern 5 4) = d25 pattern
  exact s3439 pattern
theorem s3441 (pattern : Twelve) : d1731 (change pattern 5 4) = d1289 pattern := by
  change d1300 (change pattern 5 4) = d1289 pattern
  exact s3416 pattern
theorem s3442 (pattern : Twelve) : d1736 (change pattern 5 4) = d2526 pattern := by
  change (if pattern.j then d1731 (change pattern 5 4) else d1730 (change pattern 5 4)) = d2526 pattern
  rw [s3441, s3440]
  rfl
theorem s3443 (pattern : Twelve) : d1653 (change pattern 5 4) = d821 pattern := by
  change d821 (change pattern 5 4) = d821 pattern
  exact s3413 pattern
theorem s3444 (pattern : Twelve) : d1732 (change pattern 5 4) = d821 pattern := by
  change d1653 (change pattern 5 4) = d821 pattern
  exact s3443 pattern
theorem s3445 (pattern : Twelve) : d822 (change pattern 5 4) = d822 pattern := by
  change (if pattern.i then d6 (change pattern 5 4) else d21 (change pattern 5 4)) = d822 pattern
  rw [s3278, s3412]
  rfl
theorem s3446 (pattern : Twelve) : d1655 (change pattern 5 4) = d822 pattern := by
  change d822 (change pattern 5 4) = d822 pattern
  exact s3445 pattern
theorem s3447 (pattern : Twelve) : d1733 (change pattern 5 4) = d822 pattern := by
  change d1655 (change pattern 5 4) = d822 pattern
  exact s3446 pattern
theorem s3448 (pattern : Twelve) : d1737 (change pattern 5 4) = d2527 pattern := by
  change (if pattern.j then d1733 (change pattern 5 4) else d1732 (change pattern 5 4)) = d2527 pattern
  rw [s3447, s3444]
  rfl
theorem s3449 (pattern : Twelve) : d1738 (change pattern 5 4) = d2528 pattern := by
  change (if pattern.j then d6 (change pattern 5 4) else d1731 (change pattern 5 4)) = d2528 pattern
  rw [s3278, s3441]
  rfl
end NetHack.Sokoban21.Diagram
