/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Substitutions20
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2520 (p : Pattern) : d126 (change p 10000 (some 271)) = d1246 p := by
  change (if p 186 then d125 (change p 10000 (some 271)) else d11 (change p 10000 (some 271))) = d1246 p
  rw [sub2519, sub2501]
  rfl
theorem sub2521 (p : Pattern) : d127 (change p 10000 (some 271)) = d1247 p := by
  change (if p 168 then d126 (change p 10000 (some 271)) else d120 (change p 10000 (some 271))) = d1247 p
  rw [sub2520, sub2513]
  rfl
theorem sub2522 (p : Pattern) : d128 (change p 10000 (some 271)) = d1248 p := by
  change (if p 160 then d65 (change p 10000 (some 271)) else d127 (change p 10000 (some 271))) = d1248 p
  rw [sub2517, sub2521]
  rfl
theorem sub2523 (p : Pattern) : d129 (change p 10000 (some 271)) = d1249 p := by
  change (if p 159 then d128 (change p 10000 (some 271)) else d109 (change p 10000 (some 271))) = d1249 p
  rw [sub2522, sub2518]
  rfl
theorem sub2524 (p : Pattern) : d237 (change p 10000 (some 271)) = d1250 p := by
  change (if p 158 then d129 (change p 10000 (some 271)) else d109 (change p 10000 (some 271))) = d1250 p
  rw [sub2523, sub2518]
  rfl
theorem sub2525 (p : Pattern) : d238 (change p 10000 (some 271)) = d1251 p := by
  change (if p 141 then d237 (change p 10000 (some 271)) else d179 (change p 10000 (some 271))) = d1251 p
  rw [sub2524, sub2516]
  rfl
theorem sub2526 (p : Pattern) : d239 (change p 10000 (some 271)) = d1252 p := by
  change (if p 134 then d238 (change p 10000 (some 271)) else d64 (change p 10000 (some 271))) = d1252 p
  rw [sub2525, sub2510]
  rfl
theorem sub2527 (p : Pattern) : d68 (change p 10000 (some 271)) = d68 p := by
  change (if p 158 then d55 (change p 10000 (some 271)) else d57 (change p 10000 (some 271))) = d68 p
  rw [sub2493, sub2495]
  rfl
theorem sub2528 (p : Pattern) : d69 (change p 10000 (some 271)) = d1253 p := by
  change (if p 158 then d65 (change p 10000 (some 271)) else d63 (change p 10000 (some 271))) = d1253 p
  rw [sub2517, sub2509]
  rfl
theorem sub2529 (p : Pattern) : d70 (change p 10000 (some 271)) = d1254 p := by
  change (if p 141 then d69 (change p 10000 (some 271)) else d68 (change p 10000 (some 271))) = d1254 p
  rw [sub2528, sub2527]
  rfl
theorem sub2530 (p : Pattern) : d181 (change p 10000 (some 271)) = d181 p := by
  change (if p 158 then d55 (change p 10000 (some 271)) else d122 (change p 10000 (some 271))) = d181 p
  rw [sub2493, sub2515]
  rfl
theorem sub2531 (p : Pattern) : d240 (change p 10000 (some 271)) = d1255 p := by
  change (if p 158 then d65 (change p 10000 (some 271)) else d129 (change p 10000 (some 271))) = d1255 p
  rw [sub2517, sub2523]
  rfl
theorem sub2532 (p : Pattern) : d241 (change p 10000 (some 271)) = d1256 p := by
  change (if p 141 then d240 (change p 10000 (some 271)) else d181 (change p 10000 (some 271))) = d1256 p
  rw [sub2531, sub2530]
  rfl
theorem sub2533 (p : Pattern) : d242 (change p 10000 (some 271)) = d1257 p := by
  change (if p 134 then d241 (change p 10000 (some 271)) else d70 (change p 10000 (some 271))) = d1257 p
  rw [sub2532, sub2529]
  rfl
theorem sub2534 (p : Pattern) : d243 (change p 10000 (some 271)) = d1258 p := by
  change (if p 133 then d242 (change p 10000 (some 271)) else d239 (change p 10000 (some 271))) = d1258 p
  rw [sub2533, sub2526]
  rfl
theorem sub2535 (p : Pattern) : d66 (change p 10000 (some 271)) = d1259 p := by
  change (if p 141 then d65 (change p 10000 (some 271)) else d55 (change p 10000 (some 271))) = d1259 p
  rw [sub2517, sub2493]
  rfl
theorem sub2536 (p : Pattern) : d244 (change p 10000 (some 271)) = d1260 p := by
  change (if p 133 then d66 (change p 10000 (some 271)) else d242 (change p 10000 (some 271))) = d1260 p
  rw [sub2535, sub2533]
  rfl
theorem sub2537 (p : Pattern) : d245 (change p 10000 (some 271)) = d1261 p := by
  change (if p 132 then d244 (change p 10000 (some 271)) else d243 (change p 10000 (some 271))) = d1261 p
  rw [sub2536, sub2534]
  rfl
theorem sub2538 (p : Pattern) : d137 (change p 10000 (some 271)) = d137 p := by
  change (if p 186 then d55 (change p 10000 (some 271)) else d119 (change p 10000 (some 271))) = d137 p
  rw [sub2493, sub2512]
  rfl
theorem sub2539 (p : Pattern) : d139 (change p 10000 (some 271)) = d139 p := by
  change (if p 160 then d137 (change p 10000 (some 271)) else d120 (change p 10000 (some 271))) = d139 p
  rw [sub2538, sub2513]
  rfl
theorem sub2540 (p : Pattern) : d153 (change p 10000 (some 271)) = d153 p := by
  change (if p 159 then d139 (change p 10000 (some 271)) else d57 (change p 10000 (some 271))) = d153 p
  rw [sub2539, sub2495]
  rfl
theorem sub2541 (p : Pattern) : d186 (change p 10000 (some 271)) = d186 p := by
  change (if p 158 then d153 (change p 10000 (some 271)) else d57 (change p 10000 (some 271))) = d186 p
  rw [sub2540, sub2495]
  rfl
theorem sub2542 (p : Pattern) : d143 (change p 10000 (some 271)) = d1262 p := by
  change (if p 186 then d60 (change p 10000 (some 271)) else d125 (change p 10000 (some 271))) = d1262 p
  rw [sub2506, sub2519]
  rfl
theorem sub2543 (p : Pattern) : d144 (change p 10000 (some 271)) = d1263 p := by
  change (if p 168 then d143 (change p 10000 (some 271)) else d137 (change p 10000 (some 271))) = d1263 p
  rw [sub2542, sub2538]
  rfl
theorem sub2544 (p : Pattern) : d146 (change p 10000 (some 271)) = d1264 p := by
  change (if p 160 then d144 (change p 10000 (some 271)) else d127 (change p 10000 (some 271))) = d1264 p
  rw [sub2543, sub2521]
  rfl
theorem sub2545 (p : Pattern) : d155 (change p 10000 (some 271)) = d1265 p := by
  change (if p 159 then d146 (change p 10000 (some 271)) else d63 (change p 10000 (some 271))) = d1265 p
  rw [sub2544, sub2509]
  rfl
theorem sub2546 (p : Pattern) : d246 (change p 10000 (some 271)) = d1266 p := by
  change (if p 158 then d155 (change p 10000 (some 271)) else d63 (change p 10000 (some 271))) = d1266 p
  rw [sub2545, sub2509]
  rfl
theorem sub2547 (p : Pattern) : d247 (change p 10000 (some 271)) = d1267 p := by
  change (if p 141 then d246 (change p 10000 (some 271)) else d186 (change p 10000 (some 271))) = d1267 p
  rw [sub2546, sub2541]
  rfl
theorem sub2548 (p : Pattern) : d248 (change p 10000 (some 271)) = d1268 p := by
  change (if p 134 then d66 (change p 10000 (some 271)) else d247 (change p 10000 (some 271))) = d1268 p
  rw [sub2535, sub2547]
  rfl
theorem sub2549 (p : Pattern) : d138 (change p 10000 (some 271)) = d138 p := by
  change (if p 160 then d137 (change p 10000 (some 271)) else d7 (change p 10000 (some 271))) = d138 p
  rw [sub2538, sub2490]
  rfl
theorem sub2550 (p : Pattern) : d140 (change p 10000 (some 271)) = d140 p := by
  change (if p 159 then d139 (change p 10000 (some 271)) else d138 (change p 10000 (some 271))) = d140 p
  rw [sub2539, sub2549]
  rfl
theorem sub2551 (p : Pattern) : d188 (change p 10000 (some 271)) = d188 p := by
  change (if p 158 then d55 (change p 10000 (some 271)) else d140 (change p 10000 (some 271))) = d188 p
  rw [sub2493, sub2550]
  rfl
theorem sub2552 (p : Pattern) : d145 (change p 10000 (some 271)) = d1269 p := by
  change (if p 160 then d144 (change p 10000 (some 271)) else d12 (change p 10000 (some 271))) = d1269 p
  rw [sub2543, sub2502]
  rfl
theorem sub2553 (p : Pattern) : d147 (change p 10000 (some 271)) = d1270 p := by
  change (if p 159 then d146 (change p 10000 (some 271)) else d145 (change p 10000 (some 271))) = d1270 p
  rw [sub2544, sub2552]
  rfl
theorem sub2554 (p : Pattern) : d249 (change p 10000 (some 271)) = d1271 p := by
  change (if p 158 then d65 (change p 10000 (some 271)) else d147 (change p 10000 (some 271))) = d1271 p
  rw [sub2517, sub2553]
  rfl
theorem sub2555 (p : Pattern) : d250 (change p 10000 (some 271)) = d1272 p := by
  change (if p 141 then d249 (change p 10000 (some 271)) else d188 (change p 10000 (some 271))) = d1272 p
  rw [sub2554, sub2551]
  rfl
theorem sub2556 (p : Pattern) : d251 (change p 10000 (some 271)) = d1273 p := by
  change (if p 134 then d66 (change p 10000 (some 271)) else d250 (change p 10000 (some 271))) = d1273 p
  rw [sub2535, sub2555]
  rfl
theorem sub2557 (p : Pattern) : d252 (change p 10000 (some 271)) = d1274 p := by
  change (if p 133 then d251 (change p 10000 (some 271)) else d248 (change p 10000 (some 271))) = d1274 p
  rw [sub2556, sub2548]
  rfl
theorem sub2558 (p : Pattern) : d191 (change p 10000 (some 271)) = d191 p := by
  change (if p 158 then d55 (change p 10000 (some 271)) else d153 (change p 10000 (some 271))) = d191 p
  rw [sub2493, sub2540]
  rfl
theorem sub2559 (p : Pattern) : d253 (change p 10000 (some 271)) = d1275 p := by
  change (if p 158 then d65 (change p 10000 (some 271)) else d155 (change p 10000 (some 271))) = d1275 p
  rw [sub2517, sub2545]
  rfl
theorem sub2560 (p : Pattern) : d254 (change p 10000 (some 271)) = d1276 p := by
  change (if p 141 then d253 (change p 10000 (some 271)) else d191 (change p 10000 (some 271))) = d1276 p
  rw [sub2559, sub2558]
  rfl
theorem sub2561 (p : Pattern) : d255 (change p 10000 (some 271)) = d1277 p := by
  change (if p 134 then d66 (change p 10000 (some 271)) else d254 (change p 10000 (some 271))) = d1277 p
  rw [sub2535, sub2560]
  rfl
theorem sub2562 (p : Pattern) : d256 (change p 10000 (some 271)) = d1278 p := by
  change (if p 133 then d66 (change p 10000 (some 271)) else d255 (change p 10000 (some 271))) = d1278 p
  rw [sub2535, sub2561]
  rfl
theorem sub2563 (p : Pattern) : d257 (change p 10000 (some 271)) = d1279 p := by
  change (if p 132 then d256 (change p 10000 (some 271)) else d252 (change p 10000 (some 271))) = d1279 p
  rw [sub2562, sub2557]
  rfl
theorem sub2564 (p : Pattern) : d258 (change p 10000 (some 271)) = d1280 p := by
  change (if p 108 then d257 (change p 10000 (some 271)) else d245 (change p 10000 (some 271))) = d1280 p
  rw [sub2563, sub2537]
  rfl
theorem sub2565 (p : Pattern) : d119 (change p 10000 (some 187)) = d55 p := by
  change d55 (change p 10000 (some 187)) = d55 p
  exact sub795 p
theorem sub2566 (p : Pattern) : d120 (change p 10000 (some 187)) = d56 p := by
  change (if p 186 then d119 (change p 10000 (some 187)) else d7 (change p 10000 (some 187))) = d56 p
  rw [sub2565, sub792]
  rfl
theorem sub2567 (p : Pattern) : d121 (change p 10000 (some 187)) = d452 p := by
  change (if p 160 then d55 (change p 10000 (some 187)) else d120 (change p 10000 (some 187))) = d452 p
  rw [sub795, sub2566]
  rfl
theorem sub2568 (p : Pattern) : d122 (change p 10000 (some 187)) = d1281 p := by
  change (if p 159 then d121 (change p 10000 (some 187)) else d106 (change p 10000 (some 187))) = d1281 p
  rw [sub2567, sub813]
  rfl
theorem sub2569 (p : Pattern) : d179 (change p 10000 (some 187)) = d1282 p := by
  change (if p 158 then d122 (change p 10000 (some 187)) else d106 (change p 10000 (some 187))) = d1282 p
  rw [sub2568, sub813]
  rfl
theorem sub2570 (p : Pattern) : d125 (change p 10000 (some 187)) = d60 p := by
  change d60 (change p 10000 (some 187)) = d60 p
  exact sub808 p
theorem sub2571 (p : Pattern) : d126 (change p 10000 (some 187)) = d61 p := by
  change (if p 186 then d125 (change p 10000 (some 187)) else d11 (change p 10000 (some 187))) = d61 p
  rw [sub2570, sub803]
  rfl
theorem sub2572 (p : Pattern) : d127 (change p 10000 (some 187)) = d62 p := by
  change (if p 168 then d126 (change p 10000 (some 187)) else d120 (change p 10000 (some 187))) = d62 p
  rw [sub2571, sub2566]
  rfl
theorem sub2573 (p : Pattern) : d128 (change p 10000 (some 187)) = d453 p := by
  change (if p 160 then d65 (change p 10000 (some 187)) else d127 (change p 10000 (some 187))) = d453 p
  rw [sub814, sub2572]
  rfl
theorem sub2574 (p : Pattern) : d129 (change p 10000 (some 187)) = d1283 p := by
  change (if p 159 then d128 (change p 10000 (some 187)) else d109 (change p 10000 (some 187))) = d1283 p
  rw [sub2573, sub815]
  rfl
theorem sub2575 (p : Pattern) : d237 (change p 10000 (some 187)) = d1284 p := by
  change (if p 158 then d129 (change p 10000 (some 187)) else d109 (change p 10000 (some 187))) = d1284 p
  rw [sub2574, sub815]
  rfl
theorem sub2576 (p : Pattern) : d238 (change p 10000 (some 187)) = d1285 p := by
  change (if p 141 then d237 (change p 10000 (some 187)) else d179 (change p 10000 (some 187))) = d1285 p
  rw [sub2575, sub2569]
  rfl
theorem sub2577 (p : Pattern) : d239 (change p 10000 (some 187)) = d1286 p := by
  change (if p 134 then d238 (change p 10000 (some 187)) else d64 (change p 10000 (some 187))) = d1286 p
  rw [sub2576, sub812]
  rfl
theorem sub2578 (p : Pattern) : d181 (change p 10000 (some 187)) = d1287 p := by
  change (if p 158 then d55 (change p 10000 (some 187)) else d122 (change p 10000 (some 187))) = d1287 p
  rw [sub795, sub2568]
  rfl
theorem sub2579 (p : Pattern) : d240 (change p 10000 (some 187)) = d1288 p := by
  change (if p 158 then d65 (change p 10000 (some 187)) else d129 (change p 10000 (some 187))) = d1288 p
  rw [sub814, sub2574]
  rfl
theorem sub2580 (p : Pattern) : d241 (change p 10000 (some 187)) = d1289 p := by
  change (if p 141 then d240 (change p 10000 (some 187)) else d181 (change p 10000 (some 187))) = d1289 p
  rw [sub2579, sub2578]
  rfl
theorem sub2581 (p : Pattern) : d242 (change p 10000 (some 187)) = d1290 p := by
  change (if p 134 then d241 (change p 10000 (some 187)) else d70 (change p 10000 (some 187))) = d1290 p
  rw [sub2580, sub820]
  rfl
theorem sub2582 (p : Pattern) : d243 (change p 10000 (some 187)) = d1291 p := by
  change (if p 133 then d242 (change p 10000 (some 187)) else d239 (change p 10000 (some 187))) = d1291 p
  rw [sub2581, sub2577]
  rfl
theorem sub2583 (p : Pattern) : d244 (change p 10000 (some 187)) = d1292 p := by
  change (if p 133 then d66 (change p 10000 (some 187)) else d242 (change p 10000 (some 187))) = d1292 p
  rw [sub826, sub2581]
  rfl
theorem sub2584 (p : Pattern) : d245 (change p 10000 (some 187)) = d1293 p := by
  change (if p 132 then d244 (change p 10000 (some 187)) else d243 (change p 10000 (some 187))) = d1293 p
  rw [sub2583, sub2582]
  rfl
theorem sub2585 (p : Pattern) : d137 (change p 10000 (some 187)) = d55 p := by
  change (if p 186 then d55 (change p 10000 (some 187)) else d119 (change p 10000 (some 187))) = d55 p
  rw [sub795, sub2565]
  simp only [ite_self]
theorem sub2586 (p : Pattern) : d139 (change p 10000 (some 187)) = d452 p := by
  change (if p 160 then d137 (change p 10000 (some 187)) else d120 (change p 10000 (some 187))) = d452 p
  rw [sub2585, sub2566]
  rfl
theorem sub2587 (p : Pattern) : d153 (change p 10000 (some 187)) = d1294 p := by
  change (if p 159 then d139 (change p 10000 (some 187)) else d57 (change p 10000 (some 187))) = d1294 p
  rw [sub2586, sub797]
  rfl
theorem sub2588 (p : Pattern) : d186 (change p 10000 (some 187)) = d1295 p := by
  change (if p 158 then d153 (change p 10000 (some 187)) else d57 (change p 10000 (some 187))) = d1295 p
  rw [sub2587, sub797]
  rfl
theorem sub2589 (p : Pattern) : d143 (change p 10000 (some 187)) = d60 p := by
  change (if p 186 then d60 (change p 10000 (some 187)) else d125 (change p 10000 (some 187))) = d60 p
  rw [sub808, sub2570]
  simp only [ite_self]
theorem sub2590 (p : Pattern) : d144 (change p 10000 (some 187)) = d65 p := by
  change (if p 168 then d143 (change p 10000 (some 187)) else d137 (change p 10000 (some 187))) = d65 p
  rw [sub2589, sub2585]
  rfl
theorem sub2591 (p : Pattern) : d146 (change p 10000 (some 187)) = d453 p := by
  change (if p 160 then d144 (change p 10000 (some 187)) else d127 (change p 10000 (some 187))) = d453 p
  rw [sub2590, sub2572]
  rfl
theorem sub2592 (p : Pattern) : d155 (change p 10000 (some 187)) = d1296 p := by
  change (if p 159 then d146 (change p 10000 (some 187)) else d63 (change p 10000 (some 187))) = d1296 p
  rw [sub2591, sub811]
  rfl
theorem sub2593 (p : Pattern) : d246 (change p 10000 (some 187)) = d1297 p := by
  change (if p 158 then d155 (change p 10000 (some 187)) else d63 (change p 10000 (some 187))) = d1297 p
  rw [sub2592, sub811]
  rfl
theorem sub2594 (p : Pattern) : d247 (change p 10000 (some 187)) = d1298 p := by
  change (if p 141 then d246 (change p 10000 (some 187)) else d186 (change p 10000 (some 187))) = d1298 p
  rw [sub2593, sub2588]
  rfl
theorem sub2595 (p : Pattern) : d248 (change p 10000 (some 187)) = d1299 p := by
  change (if p 134 then d66 (change p 10000 (some 187)) else d247 (change p 10000 (some 187))) = d1299 p
  rw [sub826, sub2594]
  rfl
theorem sub2596 (p : Pattern) : d138 (change p 10000 (some 187)) = d106 p := by
  change (if p 160 then d137 (change p 10000 (some 187)) else d7 (change p 10000 (some 187))) = d106 p
  rw [sub2585, sub792]
  rfl
theorem sub2597 (p : Pattern) : d140 (change p 10000 (some 187)) = d1281 p := by
  change (if p 159 then d139 (change p 10000 (some 187)) else d138 (change p 10000 (some 187))) = d1281 p
  rw [sub2586, sub2596]
  rfl
theorem sub2598 (p : Pattern) : d188 (change p 10000 (some 187)) = d1287 p := by
  change (if p 158 then d55 (change p 10000 (some 187)) else d140 (change p 10000 (some 187))) = d1287 p
  rw [sub795, sub2597]
  rfl
theorem sub2599 (p : Pattern) : d145 (change p 10000 (some 187)) = d109 p := by
  change (if p 160 then d144 (change p 10000 (some 187)) else d12 (change p 10000 (some 187))) = d109 p
  rw [sub2590, sub804]
  rfl
theorem sub2600 (p : Pattern) : d147 (change p 10000 (some 187)) = d1283 p := by
  change (if p 159 then d146 (change p 10000 (some 187)) else d145 (change p 10000 (some 187))) = d1283 p
  rw [sub2591, sub2599]
  rfl
theorem sub2601 (p : Pattern) : d249 (change p 10000 (some 187)) = d1288 p := by
  change (if p 158 then d65 (change p 10000 (some 187)) else d147 (change p 10000 (some 187))) = d1288 p
  rw [sub814, sub2600]
  rfl
theorem sub2602 (p : Pattern) : d250 (change p 10000 (some 187)) = d1289 p := by
  change (if p 141 then d249 (change p 10000 (some 187)) else d188 (change p 10000 (some 187))) = d1289 p
  rw [sub2601, sub2598]
  rfl
theorem sub2603 (p : Pattern) : d251 (change p 10000 (some 187)) = d1300 p := by
  change (if p 134 then d66 (change p 10000 (some 187)) else d250 (change p 10000 (some 187))) = d1300 p
  rw [sub826, sub2602]
  rfl
theorem sub2604 (p : Pattern) : d252 (change p 10000 (some 187)) = d1301 p := by
  change (if p 133 then d251 (change p 10000 (some 187)) else d248 (change p 10000 (some 187))) = d1301 p
  rw [sub2603, sub2595]
  rfl
theorem sub2605 (p : Pattern) : d191 (change p 10000 (some 187)) = d1302 p := by
  change (if p 158 then d55 (change p 10000 (some 187)) else d153 (change p 10000 (some 187))) = d1302 p
  rw [sub795, sub2587]
  rfl
theorem sub2606 (p : Pattern) : d253 (change p 10000 (some 187)) = d1303 p := by
  change (if p 158 then d65 (change p 10000 (some 187)) else d155 (change p 10000 (some 187))) = d1303 p
  rw [sub814, sub2592]
  rfl
theorem sub2607 (p : Pattern) : d254 (change p 10000 (some 187)) = d1304 p := by
  change (if p 141 then d253 (change p 10000 (some 187)) else d191 (change p 10000 (some 187))) = d1304 p
  rw [sub2606, sub2605]
  rfl
theorem sub2608 (p : Pattern) : d255 (change p 10000 (some 187)) = d1305 p := by
  change (if p 134 then d66 (change p 10000 (some 187)) else d254 (change p 10000 (some 187))) = d1305 p
  rw [sub826, sub2607]
  rfl
theorem sub2609 (p : Pattern) : d256 (change p 10000 (some 187)) = d1306 p := by
  change (if p 133 then d66 (change p 10000 (some 187)) else d255 (change p 10000 (some 187))) = d1306 p
  rw [sub826, sub2608]
  rfl
theorem sub2610 (p : Pattern) : d257 (change p 10000 (some 187)) = d1307 p := by
  change (if p 132 then d256 (change p 10000 (some 187)) else d252 (change p 10000 (some 187))) = d1307 p
  rw [sub2609, sub2604]
  rfl
theorem sub2611 (p : Pattern) : d258 (change p 10000 (some 187)) = d1308 p := by
  change (if p 108 then d257 (change p 10000 (some 187)) else d245 (change p 10000 (some 187))) = d1308 p
  rw [sub2610, sub2584]
  rfl
theorem sub2612 (p : Pattern) : d0 (change p 271 none) = d0 p := by
  rfl
theorem sub2613 (p : Pattern) : d35 (change p 271 none) = d0 p := by
  change d0 (change p 271 none) = d0 p
  exact sub2612 p
theorem sub2614 (p : Pattern) : d36 (change p 271 none) = d0 p := by
  change (if p 193 then d35 (change p 271 none) else d0 (change p 271 none)) = d0 p
  rw [sub2613, sub2612]
  simp only [ite_self]
theorem sub2615 (p : Pattern) : d16 (change p 271 none) = d0 p := by
  change d0 (change p 271 none) = d0 p
  exact sub2612 p
theorem sub2616 (p : Pattern) : d2 (change p 271 none) = d2 p := by
  rfl
theorem sub2617 (p : Pattern) : d9 (change p 271 none) = d2 p := by
  change d2 (change p 271 none) = d2 p
  exact sub2616 p
theorem sub2618 (p : Pattern) : d37 (change p 271 none) = d6 p := by
  change (if p 193 then d9 (change p 271 none) else d16 (change p 271 none)) = d6 p
  rw [sub2617, sub2615]
  rfl
theorem sub2619 (p : Pattern) : d38 (change p 271 none) = d7 p := by
  change (if p 192 then d37 (change p 271 none) else d36 (change p 271 none)) = d7 p
  rw [sub2618, sub2614]
  rfl
theorem sub2620 (p : Pattern) : d39 (change p 271 none) = d0 p := by
  change (if p 193 then d16 (change p 271 none) else d0 (change p 271 none)) = d0 p
  rw [sub2615, sub2612]
  simp only [ite_self]
theorem sub2621 (p : Pattern) : d40 (change p 271 none) = d7 p := by
  change (if p 192 then d37 (change p 271 none) else d39 (change p 271 none)) = d7 p
  rw [sub2618, sub2620]
  rfl
theorem sub2622 (p : Pattern) : d41 (change p 271 none) = d7 p := by
  change (if p 168 then d40 (change p 271 none) else d38 (change p 271 none)) = d7 p
  rw [sub2621, sub2619]
  simp only [ite_self]
theorem sub2623 (p : Pattern) : d659 (change p 271 none) = d2 p := by
  change d2 (change p 271 none) = d2 p
  exact sub2616 p
theorem sub2624 (p : Pattern) : d660 (change p 271 none) = d2 p := by
  change (if p 193 then d659 (change p 271 none) else d2 (change p 271 none)) = d2 p
  rw [sub2623, sub2616]
  simp only [ite_self]
theorem sub2625 (p : Pattern) : d262 (change p 271 none) = d2 p := by
  change d2 (change p 271 none) = d2 p
  exact sub2616 p
theorem sub2626 (p : Pattern) : d4 (change p 271 none) = d4 p := by
  rfl
theorem sub2627 (p : Pattern) : d58 (change p 271 none) = d4 p := by
  change d4 (change p 271 none) = d4 p
  exact sub2626 p
theorem sub2628 (p : Pattern) : d661 (change p 271 none) = d54 p := by
  change (if p 193 then d58 (change p 271 none) else d262 (change p 271 none)) = d54 p
  rw [sub2627, sub2625]
  rfl
theorem sub2629 (p : Pattern) : d662 (change p 271 none) = d55 p := by
  change (if p 192 then d661 (change p 271 none) else d660 (change p 271 none)) = d55 p
  rw [sub2628, sub2624]
  rfl
theorem sub2630 (p : Pattern) : d663 (change p 271 none) = d56 p := by
  change (if p 186 then d662 (change p 271 none) else d38 (change p 271 none)) = d56 p
  rw [sub2629, sub2619]
  rfl
theorem sub2631 (p : Pattern) : d664 (change p 271 none) = d2 p := by
  change (if p 193 then d262 (change p 271 none) else d2 (change p 271 none)) = d2 p
  rw [sub2625, sub2616]
  simp only [ite_self]
theorem sub2632 (p : Pattern) : d665 (change p 271 none) = d55 p := by
  change (if p 192 then d661 (change p 271 none) else d664 (change p 271 none)) = d55 p
  rw [sub2628, sub2631]
  rfl
theorem sub2633 (p : Pattern) : d666 (change p 271 none) = d56 p := by
  change (if p 186 then d665 (change p 271 none) else d40 (change p 271 none)) = d56 p
  rw [sub2632, sub2621]
  rfl
theorem sub2634 (p : Pattern) : d667 (change p 271 none) = d56 p := by
  change (if p 168 then d666 (change p 271 none) else d663 (change p 271 none)) = d56 p
  rw [sub2633, sub2630]
  simp only [ite_self]
theorem sub2635 (p : Pattern) : d668 (change p 271 none) = d57 p := by
  change (if p 160 then d667 (change p 271 none) else d41 (change p 271 none)) = d57 p
  rw [sub2634, sub2622]
  rfl
theorem sub2636 (p : Pattern) : d42 (change p 271 none) = d7 p := by
  change (if p 192 then d37 (change p 271 none) else d16 (change p 271 none)) = d7 p
  rw [sub2618, sub2615]
  rfl
theorem sub2637 (p : Pattern) : d43 (change p 271 none) = d7 p := by
  change (if p 168 then d42 (change p 271 none) else d40 (change p 271 none)) = d7 p
  rw [sub2636, sub2621]
  simp only [ite_self]
theorem sub2638 (p : Pattern) : d669 (change p 271 none) = d55 p := by
  change (if p 192 then d661 (change p 271 none) else d262 (change p 271 none)) = d55 p
  rw [sub2628, sub2625]
  rfl
theorem sub2639 (p : Pattern) : d670 (change p 271 none) = d56 p := by
  change (if p 186 then d669 (change p 271 none) else d42 (change p 271 none)) = d56 p
  rw [sub2638, sub2636]
  rfl
end NetHack.Sokoban12CostPartition
