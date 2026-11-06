/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Substitutions20
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem s3150 (pattern : Twelve) : d417 (change pattern 8 9) = d2476 pattern := by
  change (if pattern.d then d412 (change pattern 8 9) else d413 (change pattern 8 9)) = d2476 pattern
  rw [s3144, s3149]
  rfl
theorem s3151 (pattern : Twelve) : d420 (change pattern 8 9) = d2477 pattern := by
  change (if pattern.c then d417 (change pattern 8 9) else d407 (change pattern 8 9)) = d2477 pattern
  rw [s3150, s3148]
  rfl
theorem s3152 (pattern : Twelve) : d422 (change pattern 8 9) = d2477 pattern := by
  change (if pattern.g then d420 (change pattern 8 9) else d419 (change pattern 8 9)) = d2477 pattern
  rw [s3151, s3146]
  simp only [ite_self]
theorem s3153 (pattern : Twelve) : d423 (change pattern 8 9) = d2477 pattern := by
  change (if pattern.b then d420 (change pattern 8 9) else d422 (change pattern 8 9)) = d2477 pattern
  rw [s3151, s3152]
  simp only [ite_self]
theorem s3154 (pattern : Twelve) : d117 (change pattern 8 9) = d117 pattern := by
  change (if pattern.l then d4 (change pattern 8 9) else d3 (change pattern 8 9)) = d117 pattern
  rw [s3133, s3111]
  rfl
theorem s3155 (pattern : Twelve) : d119 (change pattern 8 9) = d119 pattern := by
  change (if pattern.k then d117 (change pattern 8 9) else d3 (change pattern 8 9)) = d119 pattern
  rw [s3154, s3111]
  rfl
theorem s3156 (pattern : Twelve) : d125 (change pattern 8 9) = d119 pattern := by
  change d119 (change pattern 8 9) = d119 pattern
  exact s3155 pattern
theorem s3157 (pattern : Twelve) : d386 (change pattern 8 9) = d2367 pattern := by
  change (if pattern.h then d125 (change pattern 8 9) else d39 (change pattern 8 9)) = d2367 pattern
  rw [s3156, s3127]
  rfl
theorem s3158 (pattern : Twelve) : d400 (change pattern 8 9) = d2426 pattern := by
  change (if pattern.f then d386 (change pattern 8 9) else d39 (change pattern 8 9)) = d2426 pattern
  rw [s3157, s3127]
  rfl
theorem s3159 (pattern : Twelve) : d47 (change pattern 8 9) = d3 pattern := by
  change d3 (change pattern 8 9) = d3 pattern
  exact s3111 pattern
theorem s3160 (pattern : Twelve) : d387 (change pattern 8 9) = d2427 pattern := by
  change (if pattern.h then d47 (change pattern 8 9) else d39 (change pattern 8 9)) = d2427 pattern
  rw [s3159, s3127]
  rfl
theorem s3161 (pattern : Twelve) : d13 (change pattern 8 9) = d13 pattern := by
  change (if pattern.l then d6 (change pattern 8 9) else d4 (change pattern 8 9)) = d13 pattern
  rw [s3143, s3133]
  rfl
theorem s3162 (pattern : Twelve) : d20 (change pattern 8 9) = d20 pattern := by
  change (if pattern.k then d13 (change pattern 8 9) else d12 (change pattern 8 9)) = d20 pattern
  rw [s3161, s3136]
  rfl
theorem s3163 (pattern : Twelve) : d128 (change pattern 8 9) = d20 pattern := by
  change d20 (change pattern 8 9) = d20 pattern
  exact s3162 pattern
theorem s3164 (pattern : Twelve) : d388 (change pattern 8 9) = d2368 pattern := by
  change (if pattern.h then d128 (change pattern 8 9) else d40 (change pattern 8 9)) = d2368 pattern
  rw [s3163, s3130]
  rfl
theorem s3165 (pattern : Twelve) : d401 (change pattern 8 9) = d2428 pattern := by
  change (if pattern.f then d388 (change pattern 8 9) else d387 (change pattern 8 9)) = d2428 pattern
  rw [s3164, s3160]
  rfl
theorem s3166 (pattern : Twelve) : d408 (change pattern 8 9) = d2429 pattern := by
  change (if pattern.e then d401 (change pattern 8 9) else d400 (change pattern 8 9)) = d2429 pattern
  rw [s3165, s3158]
  rfl
theorem s3167 (pattern : Twelve) : d414 (change pattern 8 9) = d2429 pattern := by
  change d408 (change pattern 8 9) = d2429 pattern
  exact s3166 pattern
theorem s3168 (pattern : Twelve) : d418 (change pattern 8 9) = d2478 pattern := by
  change (if pattern.d then d412 (change pattern 8 9) else d414 (change pattern 8 9)) = d2478 pattern
  rw [s3144, s3167]
  rfl
theorem s3169 (pattern : Twelve) : d421 (change pattern 8 9) = d2479 pattern := by
  change (if pattern.c then d418 (change pattern 8 9) else d407 (change pattern 8 9)) = d2479 pattern
  rw [s3168, s3148]
  rfl
theorem s3170 (pattern : Twelve) : d424 (change pattern 8 9) = d2480 pattern := by
  change (if pattern.a then d421 (change pattern 8 9) else d423 (change pattern 8 9)) = d2480 pattern
  rw [s3169, s3153]
  rfl
theorem s3171 (pattern : Twelve) : d814 (change pattern 8 9) = d814 pattern := by
  change (if pattern.k then d1 (change pattern 8 9) else d7 (change pattern 8 9)) = d814 pattern
  rw [s3101, s3102]
  rfl
theorem s3172 (pattern : Twelve) : d818 (change pattern 8 9) = d814 pattern := by
  change d814 (change pattern 8 9) = d814 pattern
  exact s3171 pattern
theorem s3173 (pattern : Twelve) : d1033 (change pattern 8 9) = d2374 pattern := by
  change (if pattern.h then d818 (change pattern 8 9) else d36 (change pattern 8 9)) = d2374 pattern
  rw [s3172, s3104]
  rfl
theorem s3174 (pattern : Twelve) : d1040 (change pattern 8 9) = d2434 pattern := by
  change (if pattern.f then d1033 (change pattern 8 9) else d377 (change pattern 8 9)) = d2434 pattern
  rw [s3173, s3108]
  rfl
theorem s3175 (pattern : Twelve) : d1032 (change pattern 8 9) = d2375 pattern := by
  change (if pattern.h then d42 (change pattern 8 9) else d29 (change pattern 8 9)) = d2375 pattern
  rw [s3138, s3114]
  rfl
theorem s3176 (pattern : Twelve) : d1041 (change pattern 8 9) = d2435 pattern := by
  change (if pattern.f then d1032 (change pattern 8 9) else d36 (change pattern 8 9)) = d2435 pattern
  rw [s3175, s3104]
  rfl
theorem s3177 (pattern : Twelve) : d1049 (change pattern 8 9) = d2436 pattern := by
  change (if pattern.e then d1041 (change pattern 8 9) else d1040 (change pattern 8 9)) = d2436 pattern
  rw [s3176, s3174]
  rfl
theorem s3178 (pattern : Twelve) : d1054 (change pattern 8 9) = d2436 pattern := by
  change d1049 (change pattern 8 9) = d2436 pattern
  exact s3177 pattern
theorem s3179 (pattern : Twelve) : d1042 (change pattern 8 9) = d2434 pattern := by
  change (if pattern.f then d1033 (change pattern 8 9) else d35 (change pattern 8 9)) = d2434 pattern
  rw [s3173, s3107]
  rfl
theorem s3180 (pattern : Twelve) : d1050 (change pattern 8 9) = d2436 pattern := by
  change (if pattern.e then d1041 (change pattern 8 9) else d1042 (change pattern 8 9)) = d2436 pattern
  rw [s3176, s3179]
  rfl
theorem s3181 (pattern : Twelve) : d1055 (change pattern 8 9) = d2436 pattern := by
  change d1050 (change pattern 8 9) = d2436 pattern
  exact s3180 pattern
theorem s3182 (pattern : Twelve) : d1060 (change pattern 8 9) = d2436 pattern := by
  change (if pattern.d then d1055 (change pattern 8 9) else d1054 (change pattern 8 9)) = d2436 pattern
  rw [s3181, s3178]
  simp only [ite_self]
theorem s3183 (pattern : Twelve) : d815 (change pattern 8 9) = d815 pattern := by
  change (if pattern.k then d3 (change pattern 8 9) else d9 (change pattern 8 9)) = d815 pattern
  rw [s3111, s3128]
  rfl
theorem s3184 (pattern : Twelve) : d820 (change pattern 8 9) = d815 pattern := by
  change d815 (change pattern 8 9) = d815 pattern
  exact s3183 pattern
theorem s3185 (pattern : Twelve) : d1034 (change pattern 8 9) = d2377 pattern := by
  change (if pattern.h then d820 (change pattern 8 9) else d40 (change pattern 8 9)) = d2377 pattern
  rw [s3184, s3130]
  rfl
theorem s3186 (pattern : Twelve) : d1044 (change pattern 8 9) = d2437 pattern := by
  change (if pattern.f then d1034 (change pattern 8 9) else d39 (change pattern 8 9)) = d2437 pattern
  rw [s3185, s3127]
  rfl
theorem s3187 (pattern : Twelve) : d14 (change pattern 8 9) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 8 9) else d5 (change pattern 8 9)) = d14 pattern
  rw [s3143, s3135]
  rfl
theorem s3188 (pattern : Twelve) : d21 (change pattern 8 9) = d21 pattern := by
  change (if pattern.k then d14 (change pattern 8 9) else d13 (change pattern 8 9)) = d21 pattern
  rw [s3187, s3161]
  rfl
theorem s3189 (pattern : Twelve) : d822 (change pattern 8 9) = d21 pattern := by
  change d21 (change pattern 8 9) = d21 pattern
  exact s3188 pattern
theorem s3190 (pattern : Twelve) : d1035 (change pattern 8 9) = d2378 pattern := by
  change (if pattern.h then d822 (change pattern 8 9) else d42 (change pattern 8 9)) = d2378 pattern
  rw [s3189, s3138]
  rfl
theorem s3191 (pattern : Twelve) : d1045 (change pattern 8 9) = d2438 pattern := by
  change (if pattern.f then d1035 (change pattern 8 9) else d40 (change pattern 8 9)) = d2438 pattern
  rw [s3190, s3130]
  rfl
theorem s3192 (pattern : Twelve) : d1052 (change pattern 8 9) = d2439 pattern := by
  change (if pattern.e then d1045 (change pattern 8 9) else d1044 (change pattern 8 9)) = d2439 pattern
  rw [s3191, s3186]
  rfl
theorem s3193 (pattern : Twelve) : d1056 (change pattern 8 9) = d2439 pattern := by
  change d1052 (change pattern 8 9) = d2439 pattern
  exact s3192 pattern
theorem s3194 (pattern : Twelve) : d1057 (change pattern 8 9) = d6 pattern := by
  change d6 (change pattern 8 9) = d6 pattern
  exact s3143 pattern
theorem s3195 (pattern : Twelve) : d1061 (change pattern 8 9) = d2481 pattern := by
  change (if pattern.d then d1057 (change pattern 8 9) else d1056 (change pattern 8 9)) = d2481 pattern
  rw [s3194, s3193]
  rfl
theorem s3196 (pattern : Twelve) : d1064 (change pattern 8 9) = d2482 pattern := by
  change (if pattern.c then d1061 (change pattern 8 9) else d1060 (change pattern 8 9)) = d2482 pattern
  rw [s3195, s3182]
  rfl
theorem s3197 (pattern : Twelve) : d1058 (change pattern 8 9) = d2439 pattern := by
  change d1052 (change pattern 8 9) = d2439 pattern
  exact s3192 pattern
theorem s3198 (pattern : Twelve) : d1062 (change pattern 8 9) = d2481 pattern := by
  change (if pattern.d then d1057 (change pattern 8 9) else d1058 (change pattern 8 9)) = d2481 pattern
  rw [s3194, s3197]
  rfl
theorem s3199 (pattern : Twelve) : d1065 (change pattern 8 9) = d2482 pattern := by
  change (if pattern.c then d1062 (change pattern 8 9) else d1050 (change pattern 8 9)) = d2482 pattern
  rw [s3198, s3180]
  rfl
theorem s3200 (pattern : Twelve) : d1067 (change pattern 8 9) = d2482 pattern := by
  change (if pattern.g then d1065 (change pattern 8 9) else d1064 (change pattern 8 9)) = d2482 pattern
  rw [s3199, s3196]
  simp only [ite_self]
theorem s3201 (pattern : Twelve) : d1068 (change pattern 8 9) = d2482 pattern := by
  change (if pattern.b then d1065 (change pattern 8 9) else d1067 (change pattern 8 9)) = d2482 pattern
  rw [s3199, s3200]
  simp only [ite_self]
theorem s3202 (pattern : Twelve) : d15 (change pattern 8 9) = d15 pattern := by
  change (if pattern.l then d5 (change pattern 8 9) else d4 (change pattern 8 9)) = d15 pattern
  rw [s3135, s3133]
  rfl
theorem s3203 (pattern : Twelve) : d873 (change pattern 8 9) = d873 pattern := by
  change (if pattern.k then d15 (change pattern 8 9) else d117 (change pattern 8 9)) = d873 pattern
  rw [s3202, s3154]
  rfl
theorem s3204 (pattern : Twelve) : d880 (change pattern 8 9) = d873 pattern := by
  change d873 (change pattern 8 9) = d873 pattern
  exact s3203 pattern
theorem s3205 (pattern : Twelve) : d1036 (change pattern 8 9) = d2384 pattern := by
  change (if pattern.h then d880 (change pattern 8 9) else d40 (change pattern 8 9)) = d2384 pattern
  rw [s3204, s3130]
  rfl
theorem s3206 (pattern : Twelve) : d1046 (change pattern 8 9) = d2444 pattern := by
  change (if pattern.f then d1036 (change pattern 8 9) else d39 (change pattern 8 9)) = d2444 pattern
  rw [s3205, s3127]
  rfl
theorem s3207 (pattern : Twelve) : d1037 (change pattern 8 9) = d2445 pattern := by
  change (if pattern.h then d125 (change pattern 8 9) else d40 (change pattern 8 9)) = d2445 pattern
  rw [s3156, s3130]
  rfl
theorem s3208 (pattern : Twelve) : d889 (change pattern 8 9) = d1690 pattern := by
  change (if pattern.h then d6 (change pattern 8 9) else d42 (change pattern 8 9)) = d1690 pattern
  rw [s3143, s3138]
  rfl
theorem s3209 (pattern : Twelve) : d1047 (change pattern 8 9) = d2446 pattern := by
  change (if pattern.f then d889 (change pattern 8 9) else d1037 (change pattern 8 9)) = d2446 pattern
  rw [s3208, s3207]
  rfl
theorem s3210 (pattern : Twelve) : d1053 (change pattern 8 9) = d2447 pattern := by
  change (if pattern.e then d1047 (change pattern 8 9) else d1046 (change pattern 8 9)) = d2447 pattern
  rw [s3209, s3206]
  rfl
theorem s3211 (pattern : Twelve) : d1059 (change pattern 8 9) = d2447 pattern := by
  change d1053 (change pattern 8 9) = d2447 pattern
  exact s3210 pattern
theorem s3212 (pattern : Twelve) : d1063 (change pattern 8 9) = d2483 pattern := by
  change (if pattern.d then d1057 (change pattern 8 9) else d1059 (change pattern 8 9)) = d2483 pattern
  rw [s3194, s3211]
  rfl
theorem s3213 (pattern : Twelve) : d1066 (change pattern 8 9) = d2484 pattern := by
  change (if pattern.c then d1063 (change pattern 8 9) else d1050 (change pattern 8 9)) = d2484 pattern
  rw [s3212, s3180]
  rfl
theorem s3214 (pattern : Twelve) : d1069 (change pattern 8 9) = d2485 pattern := by
  change (if pattern.a then d1066 (change pattern 8 9) else d1068 (change pattern 8 9)) = d2485 pattern
  rw [s3213, s3201]
  rfl
theorem s3215 (pattern : Twelve) : d8 (change pattern 8 9) = d8 pattern := by
  change (if pattern.l then d2 (change pattern 8 9) else d1 (change pattern 8 9)) = d8 pattern
  rw [s3109, s3101]
  rfl
theorem s3216 (pattern : Twelve) : d1275 (change pattern 8 9) = d1275 pattern := by
  change (if pattern.k then d8 (change pattern 8 9) else d7 (change pattern 8 9)) = d1275 pattern
  rw [s3215, s3102]
  rfl
theorem s3217 (pattern : Twelve) : d1444 (change pattern 8 9) = d1275 pattern := by
  change d1275 (change pattern 8 9) = d1275 pattern
  exact s3216 pattern
theorem s3218 (pattern : Twelve) : d872 (change pattern 8 9) = d872 pattern := by
  change (if pattern.k then d8 (change pattern 8 9) else d1 (change pattern 8 9)) = d872 pattern
  rw [s3215, s3101]
  rfl
theorem s3219 (pattern : Twelve) : d1280 (change pattern 8 9) = d872 pattern := by
  change d872 (change pattern 8 9) = d872 pattern
  exact s3218 pattern
theorem s3220 (pattern : Twelve) : d1445 (change pattern 8 9) = d2390 pattern := by
  change (if pattern.h then d1280 (change pattern 8 9) else d1444 (change pattern 8 9)) = d2390 pattern
  rw [s3219, s3217]
  rfl
theorem s3221 (pattern : Twelve) : d1450 (change pattern 8 9) = d2452 pattern := by
  change (if pattern.f then d1445 (change pattern 8 9) else d36 (change pattern 8 9)) = d2452 pattern
  rw [s3220, s3104]
  rfl
theorem s3222 (pattern : Twelve) : d1449 (change pattern 8 9) = d1294 pattern := by
  change (if pattern.f then d6 (change pattern 8 9) else d29 (change pattern 8 9)) = d1294 pattern
  rw [s3143, s3114]
  rfl
theorem s3223 (pattern : Twelve) : d1456 (change pattern 8 9) = d2453 pattern := by
  change (if pattern.e then d1449 (change pattern 8 9) else d1450 (change pattern 8 9)) = d2453 pattern
  rw [s3222, s3221]
  rfl
theorem s3224 (pattern : Twelve) : d1459 (change pattern 8 9) = d2453 pattern := by
  change d1456 (change pattern 8 9) = d2453 pattern
  exact s3223 pattern
theorem s3225 (pattern : Twelve) : d1463 (change pattern 8 9) = d2453 pattern := by
  change (if pattern.d then d1456 (change pattern 8 9) else d1459 (change pattern 8 9)) = d2453 pattern
  rw [s3223, s3224]
  simp only [ite_self]
theorem s3226 (pattern : Twelve) : d1276 (change pattern 8 9) = d1276 pattern := by
  change (if pattern.k then d117 (change pattern 8 9) else d9 (change pattern 8 9)) = d1276 pattern
  rw [s3154, s3128]
  rfl
theorem s3227 (pattern : Twelve) : d1330 (change pattern 8 9) = d1276 pattern := by
  change d1276 (change pattern 8 9) = d1276 pattern
  exact s3226 pattern
theorem s3228 (pattern : Twelve) : d1446 (change pattern 8 9) = d2392 pattern := by
  change (if pattern.h then d125 (change pattern 8 9) else d1330 (change pattern 8 9)) = d2392 pattern
  rw [s3156, s3227]
  rfl
theorem s3229 (pattern : Twelve) : d1451 (change pattern 8 9) = d2454 pattern := by
  change (if pattern.f then d1446 (change pattern 8 9) else d40 (change pattern 8 9)) = d2454 pattern
  rw [s3228, s3130]
  rfl
theorem s3230 (pattern : Twelve) : d1452 (change pattern 8 9) = d1650 pattern := by
  change (if pattern.f then d6 (change pattern 8 9) else d42 (change pattern 8 9)) = d1650 pattern
  rw [s3143, s3138]
  rfl
theorem s3231 (pattern : Twelve) : d1457 (change pattern 8 9) = d2455 pattern := by
  change (if pattern.e then d1452 (change pattern 8 9) else d1451 (change pattern 8 9)) = d2455 pattern
  rw [s3230, s3229]
  rfl
theorem s3232 (pattern : Twelve) : d1460 (change pattern 8 9) = d2455 pattern := by
  change d1457 (change pattern 8 9) = d2455 pattern
  exact s3231 pattern
theorem s3233 (pattern : Twelve) : d1461 (change pattern 8 9) = d6 pattern := by
  change d6 (change pattern 8 9) = d6 pattern
  exact s3143 pattern
theorem s3234 (pattern : Twelve) : d1464 (change pattern 8 9) = d2486 pattern := by
  change (if pattern.d then d1461 (change pattern 8 9) else d1460 (change pattern 8 9)) = d2486 pattern
  rw [s3233, s3232]
  rfl
theorem s3235 (pattern : Twelve) : d1466 (change pattern 8 9) = d2487 pattern := by
  change (if pattern.c then d1464 (change pattern 8 9) else d1463 (change pattern 8 9)) = d2487 pattern
  rw [s3234, s3225]
  rfl
theorem s3236 (pattern : Twelve) : d1467 (change pattern 8 9) = d2487 pattern := by
  change (if pattern.c then d1464 (change pattern 8 9) else d1456 (change pattern 8 9)) = d2487 pattern
  rw [s3234, s3223]
  rfl
theorem s3237 (pattern : Twelve) : d1469 (change pattern 8 9) = d2487 pattern := by
  change (if pattern.g then d1467 (change pattern 8 9) else d1466 (change pattern 8 9)) = d2487 pattern
  rw [s3236, s3235]
  simp only [ite_self]
theorem s3238 (pattern : Twelve) : d1470 (change pattern 8 9) = d2487 pattern := by
  change (if pattern.b then d1467 (change pattern 8 9) else d1469 (change pattern 8 9)) = d2487 pattern
  rw [s3236, s3237]
  simp only [ite_self]
theorem s3239 (pattern : Twelve) : d1277 (change pattern 8 9) = d1277 pattern := by
  change (if pattern.k then d14 (change pattern 8 9) else d15 (change pattern 8 9)) = d1277 pattern
  rw [s3187, s3202]
  rfl
theorem s3240 (pattern : Twelve) : d1331 (change pattern 8 9) = d1277 pattern := by
  change d1277 (change pattern 8 9) = d1277 pattern
  exact s3239 pattern
theorem s3241 (pattern : Twelve) : d1337 (change pattern 8 9) = d2398 pattern := by
  change (if pattern.h then d1331 (change pattern 8 9) else d1330 (change pattern 8 9)) = d2398 pattern
  rw [s3240, s3227]
  rfl
theorem s3242 (pattern : Twelve) : d1453 (change pattern 8 9) = d2460 pattern := by
  change (if pattern.f then d1337 (change pattern 8 9) else d40 (change pattern 8 9)) = d2460 pattern
  rw [s3241, s3130]
  rfl
theorem s3243 (pattern : Twelve) : d1447 (change pattern 8 9) = d2461 pattern := by
  change (if pattern.h then d128 (change pattern 8 9) else d42 (change pattern 8 9)) = d2461 pattern
  rw [s3163, s3138]
  rfl
theorem s3244 (pattern : Twelve) : d1454 (change pattern 8 9) = d2462 pattern := by
  change (if pattern.f then d6 (change pattern 8 9) else d1447 (change pattern 8 9)) = d2462 pattern
  rw [s3143, s3243]
  rfl
theorem s3245 (pattern : Twelve) : d1458 (change pattern 8 9) = d2463 pattern := by
  change (if pattern.e then d1454 (change pattern 8 9) else d1453 (change pattern 8 9)) = d2463 pattern
  rw [s3244, s3242]
  rfl
theorem s3246 (pattern : Twelve) : d1462 (change pattern 8 9) = d2463 pattern := by
  change d1458 (change pattern 8 9) = d2463 pattern
  exact s3245 pattern
theorem s3247 (pattern : Twelve) : d1465 (change pattern 8 9) = d2488 pattern := by
  change (if pattern.d then d1461 (change pattern 8 9) else d1462 (change pattern 8 9)) = d2488 pattern
  rw [s3233, s3246]
  rfl
theorem s3248 (pattern : Twelve) : d1468 (change pattern 8 9) = d2489 pattern := by
  change (if pattern.c then d1465 (change pattern 8 9) else d1456 (change pattern 8 9)) = d2489 pattern
  rw [s3247, s3223]
  rfl
theorem s3249 (pattern : Twelve) : d1471 (change pattern 8 9) = d2490 pattern := by
  change (if pattern.a then d1468 (change pattern 8 9) else d1470 (change pattern 8 9)) = d2490 pattern
  rw [s3248, s3238]
  rfl
theorem s3250 (pattern : Twelve) : d1324 (change pattern 8 9) = d1324 pattern := by
  change (if pattern.k then d16 (change pattern 8 9) else d11 (change pattern 8 9)) = d1324 pattern
  rw [s3134, s3112]
  rfl
theorem s3251 (pattern : Twelve) : d1645 (change pattern 8 9) = d1324 pattern := by
  change d1324 (change pattern 8 9) = d1324 pattern
  exact s3250 pattern
theorem s3252 (pattern : Twelve) : d1716 (change pattern 8 9) = d1649 pattern := by
  change (if pattern.f then d1645 (change pattern 8 9) else d29 (change pattern 8 9)) = d1649 pattern
  rw [s3251, s3114]
  rfl
theorem s3253 (pattern : Twelve) : d1719 (change pattern 8 9) = d1656 pattern := by
  change (if pattern.e then d1452 (change pattern 8 9) else d1716 (change pattern 8 9)) = d1656 pattern
  rw [s3230, s3252]
  rfl
theorem s3254 (pattern : Twelve) : d1717 (change pattern 8 9) = d1814 pattern := by
  change (if pattern.f then d128 (change pattern 8 9) else d42 (change pattern 8 9)) = d1814 pattern
  rw [s3163, s3138]
  rfl
theorem s3255 (pattern : Twelve) : d1655 (change pattern 8 9) = d1815 pattern := by
  change (if pattern.f then d6 (change pattern 8 9) else d822 (change pattern 8 9)) = d1815 pattern
  rw [s3143, s3189]
  rfl
theorem s3256 (pattern : Twelve) : d1720 (change pattern 8 9) = d1818 pattern := by
  change (if pattern.e then d1655 (change pattern 8 9) else d1717 (change pattern 8 9)) = d1818 pattern
  rw [s3255, s3254]
  rfl
theorem s3257 (pattern : Twelve) : d1722 (change pattern 8 9) = d1818 pattern := by
  change d1720 (change pattern 8 9) = d1818 pattern
  exact s3256 pattern
theorem s3258 (pattern : Twelve) : d1723 (change pattern 8 9) = d6 pattern := by
  change d6 (change pattern 8 9) = d6 pattern
  exact s3143 pattern
theorem s3259 (pattern : Twelve) : d1725 (change pattern 8 9) = d2491 pattern := by
  change (if pattern.d then d1723 (change pattern 8 9) else d1722 (change pattern 8 9)) = d2491 pattern
  rw [s3258, s3257]
  rfl
theorem s3260 (pattern : Twelve) : d1727 (change pattern 8 9) = d2492 pattern := by
  change (if pattern.c then d1725 (change pattern 8 9) else d1719 (change pattern 8 9)) = d2492 pattern
  rw [s3259, s3253]
  rfl
theorem s3261 (pattern : Twelve) : d22 (change pattern 8 9) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 8 9) else d14 (change pattern 8 9)) = d22 pattern
  rw [s3143, s3187]
  rfl
theorem s3262 (pattern : Twelve) : d183 (change pattern 8 9) = d22 pattern := by
  change d22 (change pattern 8 9) = d22 pattern
  exact s3261 pattern
theorem s3263 (pattern : Twelve) : d1667 (change pattern 8 9) = d2410 pattern := by
  change (if pattern.h then d183 (change pattern 8 9) else d128 (change pattern 8 9)) = d2410 pattern
  rw [s3262, s3163]
  rfl
theorem s3264 (pattern : Twelve) : d1718 (change pattern 8 9) = d2468 pattern := by
  change (if pattern.f then d1667 (change pattern 8 9) else d42 (change pattern 8 9)) = d2468 pattern
  rw [s3263, s3138]
  rfl
theorem s3265 (pattern : Twelve) : d1252 (change pattern 8 9) = d2469 pattern := by
  change (if pattern.h then d6 (change pattern 8 9) else d822 (change pattern 8 9)) = d2469 pattern
  rw [s3143, s3189]
  rfl
theorem s3266 (pattern : Twelve) : d1626 (change pattern 8 9) = d2470 pattern := by
  change (if pattern.f then d6 (change pattern 8 9) else d1252 (change pattern 8 9)) = d2470 pattern
  rw [s3143, s3265]
  rfl
theorem s3267 (pattern : Twelve) : d1721 (change pattern 8 9) = d2471 pattern := by
  change (if pattern.e then d1626 (change pattern 8 9) else d1718 (change pattern 8 9)) = d2471 pattern
  rw [s3266, s3264]
  rfl
theorem s3268 (pattern : Twelve) : d1724 (change pattern 8 9) = d2471 pattern := by
  change d1721 (change pattern 8 9) = d2471 pattern
  exact s3267 pattern
theorem s3269 (pattern : Twelve) : d1726 (change pattern 8 9) = d2493 pattern := by
  change (if pattern.d then d1723 (change pattern 8 9) else d1724 (change pattern 8 9)) = d2493 pattern
  rw [s3258, s3268]
  rfl
theorem s3270 (pattern : Twelve) : d1728 (change pattern 8 9) = d2494 pattern := by
  change (if pattern.c then d1726 (change pattern 8 9) else d1719 (change pattern 8 9)) = d2494 pattern
  rw [s3269, s3253]
  rfl
theorem s3271 (pattern : Twelve) : d1729 (change pattern 8 9) = d2495 pattern := by
  change (if pattern.a then d1728 (change pattern 8 9) else d1727 (change pattern 8 9)) = d2495 pattern
  rw [s3270, s3260]
  rfl
theorem s3272 (pattern : Twelve) : d0 (change pattern 5 4) = d0 pattern := by
  rfl
theorem s3273 (pattern : Twelve) : d426 (change pattern 5 4) = d0 pattern := by
  change d0 (change pattern 5 4) = d0 pattern
  exact s3272 pattern
theorem s3274 (pattern : Twelve) : d444 (change pattern 5 4) = d0 pattern := by
  change d426 (change pattern 5 4) = d0 pattern
  exact s3273 pattern
theorem s3275 (pattern : Twelve) : d2 (change pattern 5 4) = d2 pattern := by
  rfl
theorem s3276 (pattern : Twelve) : d30 (change pattern 5 4) = d30 pattern := by
  change (if pattern.i then d2 (change pattern 5 4) else d0 (change pattern 5 4)) = d30 pattern
  rw [s3275, s3272]
  rfl
theorem s3277 (pattern : Twelve) : d5 (change pattern 5 4) = d5 pattern := by
  rfl
theorem s3278 (pattern : Twelve) : d6 (change pattern 5 4) = d6 pattern := by
  rfl
theorem s3279 (pattern : Twelve) : d14 (change pattern 5 4) = d14 pattern := by
  change (if pattern.l then d6 (change pattern 5 4) else d5 (change pattern 5 4)) = d14 pattern
  rw [s3278, s3277]
  rfl
theorem s3280 (pattern : Twelve) : d22 (change pattern 5 4) = d22 pattern := by
  change (if pattern.k then d6 (change pattern 5 4) else d14 (change pattern 5 4)) = d22 pattern
  rw [s3278, s3279]
  rfl
theorem s3281 (pattern : Twelve) : d33 (change pattern 5 4) = d33 pattern := by
  change (if pattern.i then d22 (change pattern 5 4) else d0 (change pattern 5 4)) = d33 pattern
  rw [s3280, s3272]
  rfl
theorem s3282 (pattern : Twelve) : d54 (change pattern 5 4) = d54 pattern := by
  change (if pattern.h then d33 (change pattern 5 4) else d30 (change pattern 5 4)) = d54 pattern
  rw [s3281, s3276]
  rfl
theorem s3283 (pattern : Twelve) : d428 (change pattern 5 4) = d54 pattern := by
  change d54 (change pattern 5 4) = d54 pattern
  exact s3282 pattern
theorem s3284 (pattern : Twelve) : d445 (change pattern 5 4) = d54 pattern := by
  change d428 (change pattern 5 4) = d54 pattern
  exact s3283 pattern
theorem s3285 (pattern : Twelve) : d455 (change pattern 5 4) = d2497 pattern := by
  change (if pattern.j then d445 (change pattern 5 4) else d444 (change pattern 5 4)) = d2497 pattern
  rw [s3284, s3274]
  rfl
theorem s3286 (pattern : Twelve) : d430 (change pattern 5 4) = d0 pattern := by
  change d0 (change pattern 5 4) = d0 pattern
  exact s3272 pattern
theorem s3287 (pattern : Twelve) : d446 (change pattern 5 4) = d0 pattern := by
  change d430 (change pattern 5 4) = d0 pattern
  exact s3286 pattern
theorem s3288 (pattern : Twelve) : d35 (change pattern 5 4) = d35 pattern := by
  change (if pattern.i then d6 (change pattern 5 4) else d0 (change pattern 5 4)) = d35 pattern
  rw [s3278, s3272]
  rfl
theorem s3289 (pattern : Twelve) : d56 (change pattern 5 4) = d56 pattern := by
  change (if pattern.h then d35 (change pattern 5 4) else d30 (change pattern 5 4)) = d56 pattern
  rw [s3288, s3276]
  rfl
theorem s3290 (pattern : Twelve) : d432 (change pattern 5 4) = d56 pattern := by
  change d56 (change pattern 5 4) = d56 pattern
  exact s3289 pattern
theorem s3291 (pattern : Twelve) : d447 (change pattern 5 4) = d56 pattern := by
  change d432 (change pattern 5 4) = d56 pattern
  exact s3290 pattern
theorem s3292 (pattern : Twelve) : d456 (change pattern 5 4) = d2498 pattern := by
  change (if pattern.j then d447 (change pattern 5 4) else d446 (change pattern 5 4)) = d2498 pattern
  rw [s3291, s3287]
  rfl
theorem s3293 (pattern : Twelve) : d465 (change pattern 5 4) = d2499 pattern := by
  change (if pattern.d then d456 (change pattern 5 4) else d455 (change pattern 5 4)) = d2499 pattern
  rw [s3292, s3285]
  rfl
theorem s3294 (pattern : Twelve) : d434 (change pattern 5 4) = d30 pattern := by
  change d30 (change pattern 5 4) = d30 pattern
  exact s3276 pattern
theorem s3295 (pattern : Twelve) : d448 (change pattern 5 4) = d30 pattern := by
  change d434 (change pattern 5 4) = d30 pattern
  exact s3294 pattern
theorem s3296 (pattern : Twelve) : d4 (change pattern 5 4) = d4 pattern := by
  rfl
theorem s3297 (pattern : Twelve) : d38 (change pattern 5 4) = d38 pattern := by
  change (if pattern.i then d4 (change pattern 5 4) else d2 (change pattern 5 4)) = d38 pattern
  rw [s3296, s3275]
  rfl
theorem s3298 (pattern : Twelve) : d39 (change pattern 5 4) = d39 pattern := by
  change (if pattern.i then d6 (change pattern 5 4) else d2 (change pattern 5 4)) = d39 pattern
  rw [s3278, s3275]
  rfl
theorem s3299 (pattern : Twelve) : d59 (change pattern 5 4) = d59 pattern := by
  change (if pattern.h then d39 (change pattern 5 4) else d38 (change pattern 5 4)) = d59 pattern
  rw [s3298, s3297]
  rfl
end NetHack.Sokoban21.Diagram
