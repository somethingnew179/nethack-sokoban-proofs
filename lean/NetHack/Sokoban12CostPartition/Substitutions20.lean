/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions19
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2400 (p : Pattern) : d137 (change p 10000 (some 159)) = d137 p := by
  change (if p 186 then d55 (change p 10000 (some 159)) else d119 (change p 10000 (some 159))) = d137 p
  rw [sub2355, sub2374]
  rfl
theorem sub2401 (p : Pattern) : d139 (change p 10000 (some 159)) = d139 p := by
  change (if p 160 then d137 (change p 10000 (some 159)) else d120 (change p 10000 (some 159))) = d139 p
  rw [sub2400, sub2375]
  rfl
theorem sub2402 (p : Pattern) : d153 (change p 10000 (some 159)) = d139 p := by
  change d139 (change p 10000 (some 159)) = d139 p
  exact sub2401 p
theorem sub2403 (p : Pattern) : d186 (change p 10000 (some 159)) = d1203 p := by
  change (if p 158 then d153 (change p 10000 (some 159)) else d57 (change p 10000 (some 159))) = d1203 p
  rw [sub2402, sub2357]
  rfl
theorem sub2404 (p : Pattern) : d143 (change p 10000 (some 159)) = d143 p := by
  change (if p 186 then d60 (change p 10000 (some 159)) else d125 (change p 10000 (some 159))) = d143 p
  rw [sub2368, sub2381]
  rfl
theorem sub2405 (p : Pattern) : d144 (change p 10000 (some 159)) = d144 p := by
  change (if p 168 then d143 (change p 10000 (some 159)) else d137 (change p 10000 (some 159))) = d144 p
  rw [sub2404, sub2400]
  rfl
theorem sub2406 (p : Pattern) : d146 (change p 10000 (some 159)) = d146 p := by
  change (if p 160 then d144 (change p 10000 (some 159)) else d127 (change p 10000 (some 159))) = d146 p
  rw [sub2405, sub2383]
  rfl
theorem sub2407 (p : Pattern) : d155 (change p 10000 (some 159)) = d146 p := by
  change d146 (change p 10000 (some 159)) = d146 p
  exact sub2406 p
theorem sub2408 (p : Pattern) : d246 (change p 10000 (some 159)) = d1204 p := by
  change (if p 158 then d155 (change p 10000 (some 159)) else d63 (change p 10000 (some 159))) = d1204 p
  rw [sub2407, sub2371]
  rfl
theorem sub2409 (p : Pattern) : d247 (change p 10000 (some 159)) = d1205 p := by
  change (if p 141 then d246 (change p 10000 (some 159)) else d186 (change p 10000 (some 159))) = d1205 p
  rw [sub2408, sub2403]
  rfl
theorem sub2410 (p : Pattern) : d248 (change p 10000 (some 159)) = d1206 p := by
  change (if p 134 then d66 (change p 10000 (some 159)) else d247 (change p 10000 (some 159))) = d1206 p
  rw [sub2397, sub2409]
  rfl
theorem sub2411 (p : Pattern) : d140 (change p 10000 (some 159)) = d139 p := by
  change d139 (change p 10000 (some 159)) = d139 p
  exact sub2401 p
theorem sub2412 (p : Pattern) : d188 (change p 10000 (some 159)) = d1207 p := by
  change (if p 158 then d55 (change p 10000 (some 159)) else d140 (change p 10000 (some 159))) = d1207 p
  rw [sub2355, sub2411]
  rfl
theorem sub2413 (p : Pattern) : d147 (change p 10000 (some 159)) = d146 p := by
  change d146 (change p 10000 (some 159)) = d146 p
  exact sub2406 p
theorem sub2414 (p : Pattern) : d249 (change p 10000 (some 159)) = d1208 p := by
  change (if p 158 then d65 (change p 10000 (some 159)) else d147 (change p 10000 (some 159))) = d1208 p
  rw [sub2379, sub2413]
  rfl
theorem sub2415 (p : Pattern) : d250 (change p 10000 (some 159)) = d1209 p := by
  change (if p 141 then d249 (change p 10000 (some 159)) else d188 (change p 10000 (some 159))) = d1209 p
  rw [sub2414, sub2412]
  rfl
theorem sub2416 (p : Pattern) : d251 (change p 10000 (some 159)) = d1210 p := by
  change (if p 134 then d66 (change p 10000 (some 159)) else d250 (change p 10000 (some 159))) = d1210 p
  rw [sub2397, sub2415]
  rfl
theorem sub2417 (p : Pattern) : d252 (change p 10000 (some 159)) = d1211 p := by
  change (if p 133 then d251 (change p 10000 (some 159)) else d248 (change p 10000 (some 159))) = d1211 p
  rw [sub2416, sub2410]
  rfl
theorem sub2418 (p : Pattern) : d191 (change p 10000 (some 159)) = d1207 p := by
  change (if p 158 then d55 (change p 10000 (some 159)) else d153 (change p 10000 (some 159))) = d1207 p
  rw [sub2355, sub2402]
  rfl
theorem sub2419 (p : Pattern) : d253 (change p 10000 (some 159)) = d1208 p := by
  change (if p 158 then d65 (change p 10000 (some 159)) else d155 (change p 10000 (some 159))) = d1208 p
  rw [sub2379, sub2407]
  rfl
theorem sub2420 (p : Pattern) : d254 (change p 10000 (some 159)) = d1209 p := by
  change (if p 141 then d253 (change p 10000 (some 159)) else d191 (change p 10000 (some 159))) = d1209 p
  rw [sub2419, sub2418]
  rfl
theorem sub2421 (p : Pattern) : d255 (change p 10000 (some 159)) = d1210 p := by
  change (if p 134 then d66 (change p 10000 (some 159)) else d254 (change p 10000 (some 159))) = d1210 p
  rw [sub2397, sub2420]
  rfl
theorem sub2422 (p : Pattern) : d256 (change p 10000 (some 159)) = d1212 p := by
  change (if p 133 then d66 (change p 10000 (some 159)) else d255 (change p 10000 (some 159))) = d1212 p
  rw [sub2397, sub2421]
  rfl
theorem sub2423 (p : Pattern) : d257 (change p 10000 (some 159)) = d1213 p := by
  change (if p 132 then d256 (change p 10000 (some 159)) else d252 (change p 10000 (some 159))) = d1213 p
  rw [sub2422, sub2417]
  rfl
theorem sub2424 (p : Pattern) : d258 (change p 10000 (some 159)) = d1214 p := by
  change (if p 108 then d257 (change p 10000 (some 159)) else d245 (change p 10000 (some 159))) = d1214 p
  rw [sub2423, sub2399]
  rfl
theorem sub2425 (p : Pattern) : d0 (change p 186 (some 160)) = d0 p := by
  rfl
theorem sub2426 (p : Pattern) : d2 (change p 186 (some 160)) = d2 p := by
  rfl
theorem sub2427 (p : Pattern) : d6 (change p 186 (some 160)) = d6 p := by
  change (if p 193 then d2 (change p 186 (some 160)) else d0 (change p 186 (some 160))) = d6 p
  rw [sub2426, sub2425]
  rfl
theorem sub2428 (p : Pattern) : d7 (change p 186 (some 160)) = d7 p := by
  change (if p 192 then d6 (change p 186 (some 160)) else d0 (change p 186 (some 160))) = d7 p
  rw [sub2427, sub2425]
  rfl
theorem sub2429 (p : Pattern) : d56 (change p 186 (some 160)) = d7 p := by
  change d7 (change p 186 (some 160)) = d7 p
  exact sub2428 p
theorem sub2430 (p : Pattern) : d1 (change p 186 (some 160)) = d1 p := by
  rfl
theorem sub2431 (p : Pattern) : d8 (change p 186 (some 160)) = d8 p := by
  change (if p 271 then d1 (change p 186 (some 160)) else d0 (change p 186 (some 160))) = d8 p
  rw [sub2430, sub2425]
  rfl
theorem sub2432 (p : Pattern) : d3 (change p 186 (some 160)) = d3 p := by
  rfl
theorem sub2433 (p : Pattern) : d9 (change p 186 (some 160)) = d9 p := by
  change (if p 271 then d3 (change p 186 (some 160)) else d2 (change p 186 (some 160))) = d9 p
  rw [sub2432, sub2426]
  rfl
theorem sub2434 (p : Pattern) : d10 (change p 186 (some 160)) = d10 p := by
  change (if p 193 then d9 (change p 186 (some 160)) else d8 (change p 186 (some 160))) = d10 p
  rw [sub2433, sub2431]
  rfl
theorem sub2435 (p : Pattern) : d11 (change p 186 (some 160)) = d11 p := by
  change (if p 192 then d10 (change p 186 (some 160)) else d8 (change p 186 (some 160))) = d11 p
  rw [sub2434, sub2431]
  rfl
theorem sub2436 (p : Pattern) : d61 (change p 186 (some 160)) = d11 p := by
  change d11 (change p 186 (some 160)) = d11 p
  exact sub2435 p
theorem sub2437 (p : Pattern) : d62 (change p 186 (some 160)) = d12 p := by
  change (if p 168 then d61 (change p 186 (some 160)) else d56 (change p 186 (some 160))) = d12 p
  rw [sub2436, sub2429]
  rfl
theorem sub2438 (p : Pattern) : d451 (change p 186 (some 160)) = d13 p := by
  change (if p 141 then d62 (change p 186 (some 160)) else d56 (change p 186 (some 160))) = d13 p
  rw [sub2437, sub2429]
  rfl
theorem sub2439 (p : Pattern) : d4 (change p 186 (some 160)) = d4 p := by
  rfl
theorem sub2440 (p : Pattern) : d54 (change p 186 (some 160)) = d54 p := by
  change (if p 193 then d4 (change p 186 (some 160)) else d2 (change p 186 (some 160))) = d54 p
  rw [sub2439, sub2426]
  rfl
theorem sub2441 (p : Pattern) : d55 (change p 186 (some 160)) = d55 p := by
  change (if p 192 then d54 (change p 186 (some 160)) else d2 (change p 186 (some 160))) = d55 p
  rw [sub2440, sub2426]
  rfl
theorem sub2442 (p : Pattern) : d452 (change p 186 (some 160)) = d55 p := by
  change d55 (change p 186 (some 160)) = d55 p
  exact sub2441 p
theorem sub2443 (p : Pattern) : d5 (change p 186 (some 160)) = d5 p := by
  rfl
theorem sub2444 (p : Pattern) : d58 (change p 186 (some 160)) = d58 p := by
  change (if p 271 then d5 (change p 186 (some 160)) else d4 (change p 186 (some 160))) = d58 p
  rw [sub2443, sub2439]
  rfl
theorem sub2445 (p : Pattern) : d59 (change p 186 (some 160)) = d59 p := by
  change (if p 193 then d58 (change p 186 (some 160)) else d9 (change p 186 (some 160))) = d59 p
  rw [sub2444, sub2433]
  rfl
theorem sub2446 (p : Pattern) : d60 (change p 186 (some 160)) = d60 p := by
  change (if p 192 then d59 (change p 186 (some 160)) else d9 (change p 186 (some 160))) = d60 p
  rw [sub2445, sub2433]
  rfl
theorem sub2447 (p : Pattern) : d65 (change p 186 (some 160)) = d65 p := by
  change (if p 168 then d60 (change p 186 (some 160)) else d55 (change p 186 (some 160))) = d65 p
  rw [sub2446, sub2441]
  rfl
theorem sub2448 (p : Pattern) : d453 (change p 186 (some 160)) = d65 p := by
  change d65 (change p 186 (some 160)) = d65 p
  exact sub2447 p
theorem sub2449 (p : Pattern) : d454 (change p 186 (some 160)) = d66 p := by
  change (if p 141 then d453 (change p 186 (some 160)) else d452 (change p 186 (some 160))) = d66 p
  rw [sub2448, sub2442]
  rfl
theorem sub2450 (p : Pattern) : d455 (change p 186 (some 160)) = d838 p := by
  change (if p 134 then d454 (change p 186 (some 160)) else d451 (change p 186 (some 160))) = d838 p
  rw [sub2449, sub2438]
  rfl
theorem sub2451 (p : Pattern) : d456 (change p 186 (some 160)) = d832 p := by
  change (if p 158 then d55 (change p 186 (some 160)) else d56 (change p 186 (some 160))) = d832 p
  rw [sub2441, sub2429]
  rfl
theorem sub2452 (p : Pattern) : d457 (change p 186 (some 160)) = d833 p := by
  change (if p 158 then d65 (change p 186 (some 160)) else d62 (change p 186 (some 160))) = d833 p
  rw [sub2447, sub2437]
  rfl
theorem sub2453 (p : Pattern) : d458 (change p 186 (some 160)) = d834 p := by
  change (if p 141 then d457 (change p 186 (some 160)) else d456 (change p 186 (some 160))) = d834 p
  rw [sub2452, sub2451]
  rfl
theorem sub2454 (p : Pattern) : d459 (change p 186 (some 160)) = d55 p := by
  change (if p 158 then d55 (change p 186 (some 160)) else d452 (change p 186 (some 160))) = d55 p
  rw [sub2441, sub2442]
  simp only [ite_self]
theorem sub2455 (p : Pattern) : d460 (change p 186 (some 160)) = d65 p := by
  change (if p 158 then d65 (change p 186 (some 160)) else d453 (change p 186 (some 160))) = d65 p
  rw [sub2447, sub2448]
  simp only [ite_self]
theorem sub2456 (p : Pattern) : d461 (change p 186 (some 160)) = d66 p := by
  change (if p 141 then d460 (change p 186 (some 160)) else d459 (change p 186 (some 160))) = d66 p
  rw [sub2455, sub2454]
  rfl
theorem sub2457 (p : Pattern) : d462 (change p 186 (some 160)) = d839 p := by
  change (if p 134 then d461 (change p 186 (some 160)) else d458 (change p 186 (some 160))) = d839 p
  rw [sub2456, sub2453]
  rfl
theorem sub2458 (p : Pattern) : d463 (change p 186 (some 160)) = d840 p := by
  change (if p 133 then d462 (change p 186 (some 160)) else d455 (change p 186 (some 160))) = d840 p
  rw [sub2457, sub2450]
  rfl
theorem sub2459 (p : Pattern) : d66 (change p 186 (some 160)) = d66 p := by
  change (if p 141 then d65 (change p 186 (some 160)) else d55 (change p 186 (some 160))) = d66 p
  rw [sub2447, sub2441]
  rfl
theorem sub2460 (p : Pattern) : d464 (change p 186 (some 160)) = d841 p := by
  change (if p 133 then d66 (change p 186 (some 160)) else d462 (change p 186 (some 160))) = d841 p
  rw [sub2459, sub2457]
  rfl
theorem sub2461 (p : Pattern) : d465 (change p 186 (some 160)) = d842 p := by
  change (if p 132 then d464 (change p 186 (some 160)) else d463 (change p 186 (some 160))) = d842 p
  rw [sub2460, sub2458]
  rfl
theorem sub2462 (p : Pattern) : d119 (change p 186 (some 160)) = d119 p := by
  change (if p 187 then d55 (change p 186 (some 160)) else d7 (change p 186 (some 160))) = d119 p
  rw [sub2441, sub2428]
  rfl
theorem sub2463 (p : Pattern) : d137 (change p 186 (some 160)) = d119 p := by
  change d119 (change p 186 (some 160)) = d119 p
  exact sub2462 p
theorem sub2464 (p : Pattern) : d466 (change p 186 (some 160)) = d119 p := by
  change d137 (change p 186 (some 160)) = d119 p
  exact sub2463 p
theorem sub2465 (p : Pattern) : d467 (change p 186 (some 160)) = d1215 p := by
  change (if p 159 then d466 (change p 186 (some 160)) else d56 (change p 186 (some 160))) = d1215 p
  rw [sub2464, sub2429]
  rfl
theorem sub2466 (p : Pattern) : d468 (change p 186 (some 160)) = d1216 p := by
  change (if p 158 then d467 (change p 186 (some 160)) else d56 (change p 186 (some 160))) = d1216 p
  rw [sub2465, sub2429]
  rfl
theorem sub2467 (p : Pattern) : d125 (change p 186 (some 160)) = d125 p := by
  change (if p 187 then d60 (change p 186 (some 160)) else d11 (change p 186 (some 160))) = d125 p
  rw [sub2446, sub2435]
  rfl
theorem sub2468 (p : Pattern) : d143 (change p 186 (some 160)) = d125 p := by
  change d125 (change p 186 (some 160)) = d125 p
  exact sub2467 p
theorem sub2469 (p : Pattern) : d144 (change p 186 (some 160)) = d502 p := by
  change (if p 168 then d143 (change p 186 (some 160)) else d137 (change p 186 (some 160))) = d502 p
  rw [sub2468, sub2463]
  rfl
theorem sub2470 (p : Pattern) : d469 (change p 186 (some 160)) = d502 p := by
  change d144 (change p 186 (some 160)) = d502 p
  exact sub2469 p
theorem sub2471 (p : Pattern) : d470 (change p 186 (some 160)) = d1217 p := by
  change (if p 159 then d469 (change p 186 (some 160)) else d62 (change p 186 (some 160))) = d1217 p
  rw [sub2470, sub2437]
  rfl
theorem sub2472 (p : Pattern) : d471 (change p 186 (some 160)) = d1218 p := by
  change (if p 158 then d470 (change p 186 (some 160)) else d62 (change p 186 (some 160))) = d1218 p
  rw [sub2471, sub2437]
  rfl
theorem sub2473 (p : Pattern) : d472 (change p 186 (some 160)) = d1219 p := by
  change (if p 141 then d471 (change p 186 (some 160)) else d468 (change p 186 (some 160))) = d1219 p
  rw [sub2472, sub2466]
  rfl
theorem sub2474 (p : Pattern) : d473 (change p 186 (some 160)) = d1220 p := by
  change (if p 134 then d66 (change p 186 (some 160)) else d472 (change p 186 (some 160))) = d1220 p
  rw [sub2459, sub2473]
  rfl
theorem sub2475 (p : Pattern) : d474 (change p 186 (some 160)) = d1221 p := by
  change (if p 158 then d55 (change p 186 (some 160)) else d466 (change p 186 (some 160))) = d1221 p
  rw [sub2441, sub2464]
  rfl
theorem sub2476 (p : Pattern) : d475 (change p 186 (some 160)) = d1222 p := by
  change (if p 158 then d65 (change p 186 (some 160)) else d469 (change p 186 (some 160))) = d1222 p
  rw [sub2447, sub2470]
  rfl
theorem sub2477 (p : Pattern) : d476 (change p 186 (some 160)) = d1223 p := by
  change (if p 141 then d475 (change p 186 (some 160)) else d474 (change p 186 (some 160))) = d1223 p
  rw [sub2476, sub2475]
  rfl
theorem sub2478 (p : Pattern) : d477 (change p 186 (some 160)) = d1224 p := by
  change (if p 134 then d66 (change p 186 (some 160)) else d476 (change p 186 (some 160))) = d1224 p
  rw [sub2459, sub2477]
  rfl
theorem sub2479 (p : Pattern) : d478 (change p 186 (some 160)) = d1225 p := by
  change (if p 133 then d477 (change p 186 (some 160)) else d473 (change p 186 (some 160))) = d1225 p
  rw [sub2478, sub2474]
  rfl
theorem sub2480 (p : Pattern) : d479 (change p 186 (some 160)) = d1226 p := by
  change (if p 158 then d55 (change p 186 (some 160)) else d467 (change p 186 (some 160))) = d1226 p
  rw [sub2441, sub2465]
  rfl
theorem sub2481 (p : Pattern) : d480 (change p 186 (some 160)) = d1227 p := by
  change (if p 158 then d65 (change p 186 (some 160)) else d470 (change p 186 (some 160))) = d1227 p
  rw [sub2447, sub2471]
  rfl
theorem sub2482 (p : Pattern) : d481 (change p 186 (some 160)) = d1228 p := by
  change (if p 141 then d480 (change p 186 (some 160)) else d479 (change p 186 (some 160))) = d1228 p
  rw [sub2481, sub2480]
  rfl
theorem sub2483 (p : Pattern) : d482 (change p 186 (some 160)) = d1229 p := by
  change (if p 134 then d66 (change p 186 (some 160)) else d481 (change p 186 (some 160))) = d1229 p
  rw [sub2459, sub2482]
  rfl
theorem sub2484 (p : Pattern) : d483 (change p 186 (some 160)) = d1230 p := by
  change (if p 133 then d66 (change p 186 (some 160)) else d482 (change p 186 (some 160))) = d1230 p
  rw [sub2459, sub2483]
  rfl
theorem sub2485 (p : Pattern) : d484 (change p 186 (some 160)) = d1231 p := by
  change (if p 132 then d483 (change p 186 (some 160)) else d478 (change p 186 (some 160))) = d1231 p
  rw [sub2484, sub2479]
  rfl
theorem sub2486 (p : Pattern) : d485 (change p 186 (some 160)) = d1232 p := by
  change (if p 108 then d484 (change p 186 (some 160)) else d465 (change p 186 (some 160))) = d1232 p
  rw [sub2485, sub2461]
  rfl
theorem sub2487 (p : Pattern) : d0 (change p 10000 (some 271)) = d0 p := by
  rfl
theorem sub2488 (p : Pattern) : d2 (change p 10000 (some 271)) = d2 p := by
  rfl
theorem sub2489 (p : Pattern) : d6 (change p 10000 (some 271)) = d6 p := by
  change (if p 193 then d2 (change p 10000 (some 271)) else d0 (change p 10000 (some 271))) = d6 p
  rw [sub2488, sub2487]
  rfl
theorem sub2490 (p : Pattern) : d7 (change p 10000 (some 271)) = d7 p := by
  change (if p 192 then d6 (change p 10000 (some 271)) else d0 (change p 10000 (some 271))) = d7 p
  rw [sub2489, sub2487]
  rfl
theorem sub2491 (p : Pattern) : d4 (change p 10000 (some 271)) = d4 p := by
  rfl
theorem sub2492 (p : Pattern) : d54 (change p 10000 (some 271)) = d54 p := by
  change (if p 193 then d4 (change p 10000 (some 271)) else d2 (change p 10000 (some 271))) = d54 p
  rw [sub2491, sub2488]
  rfl
theorem sub2493 (p : Pattern) : d55 (change p 10000 (some 271)) = d55 p := by
  change (if p 192 then d54 (change p 10000 (some 271)) else d2 (change p 10000 (some 271))) = d55 p
  rw [sub2492, sub2488]
  rfl
theorem sub2494 (p : Pattern) : d56 (change p 10000 (some 271)) = d56 p := by
  change (if p 186 then d55 (change p 10000 (some 271)) else d7 (change p 10000 (some 271))) = d56 p
  rw [sub2493, sub2490]
  rfl
theorem sub2495 (p : Pattern) : d57 (change p 10000 (some 271)) = d57 p := by
  change (if p 160 then d56 (change p 10000 (some 271)) else d7 (change p 10000 (some 271))) = d57 p
  rw [sub2494, sub2490]
  rfl
theorem sub2496 (p : Pattern) : d1 (change p 10000 (some 271)) = d1 p := by
  rfl
theorem sub2497 (p : Pattern) : d8 (change p 10000 (some 271)) = d1 p := by
  change d1 (change p 10000 (some 271)) = d1 p
  exact sub2496 p
theorem sub2498 (p : Pattern) : d3 (change p 10000 (some 271)) = d3 p := by
  rfl
theorem sub2499 (p : Pattern) : d9 (change p 10000 (some 271)) = d3 p := by
  change d3 (change p 10000 (some 271)) = d3 p
  exact sub2498 p
theorem sub2500 (p : Pattern) : d10 (change p 10000 (some 271)) = d1234 p := by
  change (if p 193 then d9 (change p 10000 (some 271)) else d8 (change p 10000 (some 271))) = d1234 p
  rw [sub2499, sub2497]
  rfl
theorem sub2501 (p : Pattern) : d11 (change p 10000 (some 271)) = d1235 p := by
  change (if p 192 then d10 (change p 10000 (some 271)) else d8 (change p 10000 (some 271))) = d1235 p
  rw [sub2500, sub2497]
  rfl
theorem sub2502 (p : Pattern) : d12 (change p 10000 (some 271)) = d1236 p := by
  change (if p 168 then d11 (change p 10000 (some 271)) else d7 (change p 10000 (some 271))) = d1236 p
  rw [sub2501, sub2490]
  rfl
theorem sub2503 (p : Pattern) : d5 (change p 10000 (some 271)) = d5 p := by
  rfl
theorem sub2504 (p : Pattern) : d58 (change p 10000 (some 271)) = d5 p := by
  change d5 (change p 10000 (some 271)) = d5 p
  exact sub2503 p
theorem sub2505 (p : Pattern) : d59 (change p 10000 (some 271)) = d1237 p := by
  change (if p 193 then d58 (change p 10000 (some 271)) else d9 (change p 10000 (some 271))) = d1237 p
  rw [sub2504, sub2499]
  rfl
theorem sub2506 (p : Pattern) : d60 (change p 10000 (some 271)) = d1238 p := by
  change (if p 192 then d59 (change p 10000 (some 271)) else d9 (change p 10000 (some 271))) = d1238 p
  rw [sub2505, sub2499]
  rfl
theorem sub2507 (p : Pattern) : d61 (change p 10000 (some 271)) = d1239 p := by
  change (if p 186 then d60 (change p 10000 (some 271)) else d11 (change p 10000 (some 271))) = d1239 p
  rw [sub2506, sub2501]
  rfl
theorem sub2508 (p : Pattern) : d62 (change p 10000 (some 271)) = d1240 p := by
  change (if p 168 then d61 (change p 10000 (some 271)) else d56 (change p 10000 (some 271))) = d1240 p
  rw [sub2507, sub2494]
  rfl
theorem sub2509 (p : Pattern) : d63 (change p 10000 (some 271)) = d1241 p := by
  change (if p 160 then d62 (change p 10000 (some 271)) else d12 (change p 10000 (some 271))) = d1241 p
  rw [sub2508, sub2502]
  rfl
theorem sub2510 (p : Pattern) : d64 (change p 10000 (some 271)) = d1242 p := by
  change (if p 141 then d63 (change p 10000 (some 271)) else d57 (change p 10000 (some 271))) = d1242 p
  rw [sub2509, sub2495]
  rfl
theorem sub2511 (p : Pattern) : d106 (change p 10000 (some 271)) = d106 p := by
  change (if p 160 then d55 (change p 10000 (some 271)) else d7 (change p 10000 (some 271))) = d106 p
  rw [sub2493, sub2490]
  rfl
theorem sub2512 (p : Pattern) : d119 (change p 10000 (some 271)) = d119 p := by
  change (if p 187 then d55 (change p 10000 (some 271)) else d7 (change p 10000 (some 271))) = d119 p
  rw [sub2493, sub2490]
  rfl
theorem sub2513 (p : Pattern) : d120 (change p 10000 (some 271)) = d120 p := by
  change (if p 186 then d119 (change p 10000 (some 271)) else d7 (change p 10000 (some 271))) = d120 p
  rw [sub2512, sub2490]
  rfl
theorem sub2514 (p : Pattern) : d121 (change p 10000 (some 271)) = d121 p := by
  change (if p 160 then d55 (change p 10000 (some 271)) else d120 (change p 10000 (some 271))) = d121 p
  rw [sub2493, sub2513]
  rfl
theorem sub2515 (p : Pattern) : d122 (change p 10000 (some 271)) = d122 p := by
  change (if p 159 then d121 (change p 10000 (some 271)) else d106 (change p 10000 (some 271))) = d122 p
  rw [sub2514, sub2511]
  rfl
theorem sub2516 (p : Pattern) : d179 (change p 10000 (some 271)) = d179 p := by
  change (if p 158 then d122 (change p 10000 (some 271)) else d106 (change p 10000 (some 271))) = d179 p
  rw [sub2515, sub2511]
  rfl
theorem sub2517 (p : Pattern) : d65 (change p 10000 (some 271)) = d1243 p := by
  change (if p 168 then d60 (change p 10000 (some 271)) else d55 (change p 10000 (some 271))) = d1243 p
  rw [sub2506, sub2493]
  rfl
theorem sub2518 (p : Pattern) : d109 (change p 10000 (some 271)) = d1244 p := by
  change (if p 160 then d65 (change p 10000 (some 271)) else d12 (change p 10000 (some 271))) = d1244 p
  rw [sub2517, sub2502]
  rfl
theorem sub2519 (p : Pattern) : d125 (change p 10000 (some 271)) = d1245 p := by
  change (if p 187 then d60 (change p 10000 (some 271)) else d11 (change p 10000 (some 271))) = d1245 p
  rw [sub2506, sub2501]
  rfl
end NetHack.Sokoban12CostPartition
