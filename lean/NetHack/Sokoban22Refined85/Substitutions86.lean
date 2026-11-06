/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions85
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub10320 (p : Pattern) : d2412 (change p 224 none) = d178 p := by
  change (if p 161 then d2411 (change p 224 none) else d2409 (change p 224 none)) = d178 p
  rw [sub10319, sub10317]
  rfl
theorem sub10321 (p : Pattern) : d2413 (change p 224 none) = d179 p := by
  change (if p 160 then d2412 (change p 224 none) else d2274 (change p 224 none)) = d179 p
  rw [sub10320, sub10170]
  rfl
theorem sub10322 (p : Pattern) : d2414 (change p 224 none) = d180 p := by
  change (if p 163 then d2219 (change p 224 none) else d2404 (change p 224 none)) = d180 p
  rw [sub10112, sub10312]
  rfl
theorem sub10323 (p : Pattern) : d2415 (change p 224 none) = d181 p := by
  change (if p 163 then d2250 (change p 224 none) else d2407 (change p 224 none)) = d181 p
  rw [sub10146, sub10315]
  rfl
theorem sub10324 (p : Pattern) : d2416 (change p 224 none) = d182 p := by
  change (if p 162 then d2415 (change p 224 none) else d2414 (change p 224 none)) = d182 p
  rw [sub10323, sub10322]
  rfl
theorem sub10325 (p : Pattern) : d2417 (change p 224 none) = d183 p := by
  change (if p 163 then d12 (change p 224 none) else d2407 (change p 224 none)) = d183 p
  rw [sub10059, sub10315]
  rfl
theorem sub10326 (p : Pattern) : d2418 (change p 224 none) = d184 p := by
  change (if p 162 then d12 (change p 224 none) else d2417 (change p 224 none)) = d184 p
  rw [sub10059, sub10325]
  rfl
theorem sub10327 (p : Pattern) : d2419 (change p 224 none) = d185 p := by
  change (if p 161 then d2418 (change p 224 none) else d2416 (change p 224 none)) = d185 p
  rw [sub10326, sub10324]
  rfl
theorem sub10328 (p : Pattern) : d2420 (change p 224 none) = d186 p := by
  change (if p 160 then d2419 (change p 224 none) else d2265 (change p 224 none)) = d186 p
  rw [sub10327, sub10161]
  rfl
theorem sub10329 (p : Pattern) : d2421 (change p 224 none) = d187 p := by
  change (if p 141 then d2420 (change p 224 none) else d2413 (change p 224 none)) = d187 p
  rw [sub10328, sub10321]
  rfl
theorem sub10330 (p : Pattern) : d2422 (change p 224 none) = d188 p := by
  change (if p 162 then d2259 (change p 224 none) else d2201 (change p 224 none)) = d188 p
  rw [sub10155, sub10082]
  rfl
theorem sub10331 (p : Pattern) : d2423 (change p 224 none) = d189 p := by
  change (if p 161 then d2260 (change p 224 none) else d2422 (change p 224 none)) = d189 p
  rw [sub10156, sub10330]
  rfl
theorem sub10332 (p : Pattern) : d8 (change p 224 none) = d8 p := by
  rfl
theorem sub10333 (p : Pattern) : d190 (change p 224 none) = d190 p := by
  change (if p 247 then d12 (change p 224 none) else d8 (change p 224 none)) = d190 p
  rw [sub10059, sub10332]
  rfl
theorem sub10334 (p : Pattern) : d191 (change p 224 none) = d191 p := by
  change (if p 246 then d190 (change p 224 none) else d8 (change p 224 none)) = d191 p
  rw [sub10333, sub10332]
  rfl
theorem sub10335 (p : Pattern) : d2424 (change p 224 none) = d191 p := by
  change d191 (change p 224 none) = d191 p
  exact sub10334 p
theorem sub10336 (p : Pattern) : d2425 (change p 224 none) = d192 p := by
  change (if p 204 then d12 (change p 224 none) else d2424 (change p 224 none)) = d192 p
  rw [sub10059, sub10335]
  rfl
theorem sub10337 (p : Pattern) : d2426 (change p 224 none) = d193 p := by
  change (if p 182 then d2425 (change p 224 none) else d2424 (change p 224 none)) = d193 p
  rw [sub10336, sub10335]
  rfl
theorem sub10338 (p : Pattern) : d2427 (change p 224 none) = d194 p := by
  change (if p 163 then d2426 (change p 224 none) else d2198 (change p 224 none)) = d194 p
  rw [sub10337, sub10079]
  rfl
theorem sub10339 (p : Pattern) : d2428 (change p 224 none) = d195 p := by
  change (if p 162 then d12 (change p 224 none) else d2427 (change p 224 none)) = d195 p
  rw [sub10059, sub10338]
  rfl
theorem sub10340 (p : Pattern) : d2429 (change p 224 none) = d196 p := by
  change (if p 161 then d12 (change p 224 none) else d2428 (change p 224 none)) = d196 p
  rw [sub10059, sub10339]
  rfl
theorem sub10341 (p : Pattern) : d2430 (change p 224 none) = d197 p := by
  change (if p 160 then d2429 (change p 224 none) else d2423 (change p 224 none)) = d197 p
  rw [sub10340, sub10331]
  rfl
theorem sub10342 (p : Pattern) : d2431 (change p 224 none) = d198 p := by
  change (if p 163 then d2240 (change p 224 none) else d2198 (change p 224 none)) = d198 p
  rw [sub10136, sub10079]
  rfl
theorem sub10343 (p : Pattern) : d2432 (change p 224 none) = d199 p := by
  change (if p 162 then d2431 (change p 224 none) else d2232 (change p 224 none)) = d199 p
  rw [sub10342, sub10125]
  rfl
theorem sub10344 (p : Pattern) : d2433 (change p 224 none) = d200 p := by
  change (if p 161 then d2267 (change p 224 none) else d2432 (change p 224 none)) = d200 p
  rw [sub10163, sub10343]
  rfl
theorem sub10345 (p : Pattern) : d2434 (change p 224 none) = d201 p := by
  change (if p 163 then d12 (change p 224 none) else d2426 (change p 224 none)) = d201 p
  rw [sub10059, sub10337]
  rfl
theorem sub10346 (p : Pattern) : d2435 (change p 224 none) = d202 p := by
  change (if p 162 then d12 (change p 224 none) else d2434 (change p 224 none)) = d202 p
  rw [sub10059, sub10345]
  rfl
theorem sub10347 (p : Pattern) : d2436 (change p 224 none) = d203 p := by
  change (if p 161 then d12 (change p 224 none) else d2435 (change p 224 none)) = d203 p
  rw [sub10059, sub10346]
  rfl
theorem sub10348 (p : Pattern) : d2437 (change p 224 none) = d204 p := by
  change (if p 160 then d2436 (change p 224 none) else d2433 (change p 224 none)) = d204 p
  rw [sub10347, sub10344]
  rfl
theorem sub10349 (p : Pattern) : d2438 (change p 224 none) = d205 p := by
  change (if p 141 then d2437 (change p 224 none) else d2430 (change p 224 none)) = d205 p
  rw [sub10348, sub10341]
  rfl
theorem sub10350 (p : Pattern) : d2439 (change p 224 none) = d206 p := by
  change (if p 138 then d2438 (change p 224 none) else d2421 (change p 224 none)) = d206 p
  rw [sub10349, sub10329]
  rfl
theorem sub10351 (p : Pattern) : d2440 (change p 224 none) = d207 p := by
  change (if p 138 then d12 (change p 224 none) else d2438 (change p 224 none)) = d207 p
  rw [sub10059, sub10349]
  rfl
theorem sub10352 (p : Pattern) : d2441 (change p 224 none) = d208 p := by
  change (if p 116 then d2440 (change p 224 none) else d2439 (change p 224 none)) = d208 p
  rw [sub10351, sub10350]
  rfl
theorem sub10353 (p : Pattern) : d2442 (change p 224 none) = d209 p := by
  change (if p 115 then d2441 (change p 224 none) else d2311 (change p 224 none)) = d209 p
  rw [sub10352, sub10207]
  rfl
theorem sub10354 (p : Pattern) : d2443 (change p 224 none) = d210 p := by
  change (if p 71 then d2442 (change p 224 none) else d2296 (change p 224 none)) = d210 p
  rw [sub10353, sub10192]
  rfl
theorem sub10355 (p : Pattern) : d2444 (change p 224 none) = d211 p := by
  change (if p 163 then d12 (change p 224 none) else d2330 (change p 224 none)) = d211 p
  rw [sub10059, sub10232]
  rfl
theorem sub10356 (p : Pattern) : d2445 (change p 224 none) = d212 p := by
  change (if p 162 then d2444 (change p 224 none) else d2355 (change p 224 none)) = d212 p
  rw [sub10355, sub10263]
  rfl
theorem sub10357 (p : Pattern) : d2446 (change p 224 none) = d213 p := by
  change (if p 162 then d12 (change p 224 none) else d2444 (change p 224 none)) = d213 p
  rw [sub10059, sub10355]
  rfl
theorem sub10358 (p : Pattern) : d2447 (change p 224 none) = d214 p := by
  change (if p 161 then d2446 (change p 224 none) else d2445 (change p 224 none)) = d214 p
  rw [sub10357, sub10356]
  rfl
theorem sub10359 (p : Pattern) : d2448 (change p 224 none) = d215 p := by
  change (if p 163 then d12 (change p 224 none) else d2344 (change p 224 none)) = d215 p
  rw [sub10059, sub10252]
  rfl
theorem sub10360 (p : Pattern) : d2449 (change p 224 none) = d216 p := by
  change (if p 162 then d2448 (change p 224 none) else d2362 (change p 224 none)) = d216 p
  rw [sub10359, sub10270]
  rfl
theorem sub10361 (p : Pattern) : d2450 (change p 224 none) = d217 p := by
  change (if p 162 then d12 (change p 224 none) else d2448 (change p 224 none)) = d217 p
  rw [sub10059, sub10359]
  rfl
theorem sub10362 (p : Pattern) : d2451 (change p 224 none) = d218 p := by
  change (if p 161 then d2450 (change p 224 none) else d2449 (change p 224 none)) = d218 p
  rw [sub10361, sub10360]
  rfl
theorem sub10363 (p : Pattern) : d2452 (change p 224 none) = d219 p := by
  change (if p 160 then d2451 (change p 224 none) else d2447 (change p 224 none)) = d219 p
  rw [sub10362, sub10358]
  rfl
theorem sub10364 (p : Pattern) : d2453 (change p 224 none) = d220 p := by
  change (if p 141 then d2452 (change p 224 none) else d2350 (change p 224 none)) = d220 p
  rw [sub10363, sub10258]
  rfl
theorem sub10365 (p : Pattern) : d2454 (change p 224 none) = d212 p := by
  change (if p 162 then d2444 (change p 224 none) else d2377 (change p 224 none)) = d212 p
  rw [sub10355, sub10285]
  rfl
theorem sub10366 (p : Pattern) : d2455 (change p 224 none) = d214 p := by
  change (if p 161 then d2446 (change p 224 none) else d2454 (change p 224 none)) = d214 p
  rw [sub10357, sub10365]
  rfl
theorem sub10367 (p : Pattern) : d2456 (change p 224 none) = d221 p := by
  change (if p 160 then d2382 (change p 224 none) else d2455 (change p 224 none)) = d221 p
  rw [sub10290, sub10366]
  rfl
theorem sub10368 (p : Pattern) : d2457 (change p 224 none) = d222 p := by
  change (if p 141 then d2456 (change p 224 none) else d2376 (change p 224 none)) = d222 p
  rw [sub10367, sub10284]
  rfl
theorem sub10369 (p : Pattern) : d2458 (change p 224 none) = d223 p := by
  change (if p 138 then d2457 (change p 224 none) else d2453 (change p 224 none)) = d223 p
  rw [sub10368, sub10364]
  rfl
theorem sub10370 (p : Pattern) : d2459 (change p 224 none) = d224 p := by
  change (if p 138 then d2389 (change p 224 none) else d2457 (change p 224 none)) = d224 p
  rw [sub10297, sub10368]
  rfl
theorem sub10371 (p : Pattern) : d2460 (change p 224 none) = d225 p := by
  change (if p 116 then d2459 (change p 224 none) else d2458 (change p 224 none)) = d225 p
  rw [sub10370, sub10369]
  rfl
theorem sub10372 (p : Pattern) : d2461 (change p 224 none) = d226 p := by
  change (if p 182 then d2340 (change p 224 none) else d2336 (change p 224 none)) = d226 p
  rw [sub10248, sub10241]
  rfl
theorem sub10373 (p : Pattern) : d2462 (change p 224 none) = d227 p := by
  change (if p 163 then d2461 (change p 224 none) else d2354 (change p 224 none)) = d227 p
  rw [sub10372, sub10262]
  rfl
theorem sub10374 (p : Pattern) : d2463 (change p 224 none) = d228 p := by
  change (if p 162 then d2448 (change p 224 none) else d2462 (change p 224 none)) = d228 p
  rw [sub10359, sub10373]
  rfl
theorem sub10375 (p : Pattern) : d2464 (change p 224 none) = d229 p := by
  change (if p 182 then d12 (change p 224 none) else d2339 (change p 224 none)) = d229 p
  rw [sub10059, sub10247]
  rfl
theorem sub10376 (p : Pattern) : d2465 (change p 224 none) = d230 p := by
  change (if p 163 then d12 (change p 224 none) else d2464 (change p 224 none)) = d230 p
  rw [sub10059, sub10375]
  rfl
theorem sub10377 (p : Pattern) : d2466 (change p 224 none) = d231 p := by
  change (if p 162 then d12 (change p 224 none) else d2465 (change p 224 none)) = d231 p
  rw [sub10059, sub10376]
  rfl
theorem sub10378 (p : Pattern) : d2467 (change p 224 none) = d232 p := by
  change (if p 161 then d2466 (change p 224 none) else d2463 (change p 224 none)) = d232 p
  rw [sub10377, sub10374]
  rfl
theorem sub10379 (p : Pattern) : d2468 (change p 224 none) = d233 p := by
  change (if p 160 then d2467 (change p 224 none) else d2394 (change p 224 none)) = d233 p
  rw [sub10378, sub10302]
  rfl
theorem sub10380 (p : Pattern) : d2469 (change p 224 none) = d234 p := by
  change (if p 182 then d2340 (change p 224 none) else d2328 (change p 224 none)) = d234 p
  rw [sub10248, sub10230]
  rfl
theorem sub10381 (p : Pattern) : d2470 (change p 224 none) = d235 p := by
  change (if p 163 then d2344 (change p 224 none) else d2469 (change p 224 none)) = d235 p
  rw [sub10252, sub10380]
  rfl
theorem sub10382 (p : Pattern) : d2471 (change p 224 none) = d236 p := by
  change (if p 162 then d2465 (change p 224 none) else d2470 (change p 224 none)) = d236 p
  rw [sub10376, sub10381]
  rfl
theorem sub10383 (p : Pattern) : d2472 (change p 224 none) = d237 p := by
  change (if p 162 then d12 (change p 224 none) else d2225 (change p 224 none)) = d237 p
  rw [sub10059, sub10118]
  rfl
theorem sub10384 (p : Pattern) : d2473 (change p 224 none) = d238 p := by
  change (if p 161 then d2472 (change p 224 none) else d2471 (change p 224 none)) = d238 p
  rw [sub10383, sub10382]
  rfl
theorem sub10385 (p : Pattern) : d2474 (change p 224 none) = d239 p := by
  change (if p 160 then d2473 (change p 224 none) else d2455 (change p 224 none)) = d239 p
  rw [sub10384, sub10366]
  rfl
theorem sub10386 (p : Pattern) : d2475 (change p 224 none) = d240 p := by
  change (if p 141 then d2474 (change p 224 none) else d2468 (change p 224 none)) = d240 p
  rw [sub10385, sub10379]
  rfl
theorem sub10387 (p : Pattern) : d2476 (change p 224 none) = d241 p := by
  change (if p 163 then d2240 (change p 224 none) else d2354 (change p 224 none)) = d241 p
  rw [sub10136, sub10262]
  rfl
theorem sub10388 (p : Pattern) : d2477 (change p 224 none) = d242 p := by
  change (if p 162 then d2476 (change p 224 none) else d2327 (change p 224 none)) = d242 p
  rw [sub10387, sub10226]
  rfl
theorem sub10389 (p : Pattern) : d2478 (change p 224 none) = d243 p := by
  change (if p 161 then d2359 (change p 224 none) else d2477 (change p 224 none)) = d243 p
  rw [sub10267, sub10388]
  rfl
theorem sub10390 (p : Pattern) : d2479 (change p 224 none) = d244 p := by
  change (if p 160 then d2382 (change p 224 none) else d2478 (change p 224 none)) = d244 p
  rw [sub10290, sub10389]
  rfl
theorem sub10391 (p : Pattern) : d2480 (change p 224 none) = d245 p := by
  change (if p 162 then d2444 (change p 224 none) else d2354 (change p 224 none)) = d245 p
  rw [sub10355, sub10262]
  rfl
theorem sub10392 (p : Pattern) : d2481 (change p 224 none) = d246 p := by
  change (if p 161 then d2381 (change p 224 none) else d2480 (change p 224 none)) = d246 p
  rw [sub10289, sub10391]
  rfl
theorem sub10393 (p : Pattern) : d2482 (change p 224 none) = d247 p := by
  change (if p 162 then d12 (change p 224 none) else d2206 (change p 224 none)) = d247 p
  rw [sub10059, sub10090]
  rfl
theorem sub10394 (p : Pattern) : d2483 (change p 224 none) = d248 p := by
  change (if p 161 then d12 (change p 224 none) else d2482 (change p 224 none)) = d248 p
  rw [sub10059, sub10393]
  rfl
theorem sub10395 (p : Pattern) : d2484 (change p 224 none) = d249 p := by
  change (if p 160 then d2483 (change p 224 none) else d2481 (change p 224 none)) = d249 p
  rw [sub10394, sub10392]
  rfl
theorem sub10396 (p : Pattern) : d2485 (change p 224 none) = d250 p := by
  change (if p 141 then d2484 (change p 224 none) else d2479 (change p 224 none)) = d250 p
  rw [sub10395, sub10390]
  rfl
theorem sub10397 (p : Pattern) : d2486 (change p 224 none) = d251 p := by
  change (if p 138 then d2485 (change p 224 none) else d2475 (change p 224 none)) = d251 p
  rw [sub10396, sub10386]
  rfl
theorem sub10398 (p : Pattern) : d2487 (change p 224 none) = d252 p := by
  change (if p 163 then d2205 (change p 224 none) else d2354 (change p 224 none)) = d252 p
  rw [sub10089, sub10262]
  rfl
theorem sub10399 (p : Pattern) : d2488 (change p 224 none) = d253 p := by
  change (if p 162 then d2487 (change p 224 none) else d2327 (change p 224 none)) = d253 p
  rw [sub10398, sub10226]
  rfl
theorem sub10400 (p : Pattern) : d2489 (change p 224 none) = d254 p := by
  change (if p 163 then d2205 (change p 224 none) else d2330 (change p 224 none)) = d254 p
  rw [sub10089, sub10232]
  rfl
theorem sub10401 (p : Pattern) : d2490 (change p 224 none) = d255 p := by
  change (if p 162 then d12 (change p 224 none) else d2489 (change p 224 none)) = d255 p
  rw [sub10059, sub10400]
  rfl
theorem sub10402 (p : Pattern) : d2491 (change p 224 none) = d256 p := by
  change (if p 161 then d2490 (change p 224 none) else d2488 (change p 224 none)) = d256 p
  rw [sub10401, sub10399]
  rfl
theorem sub10403 (p : Pattern) : d2492 (change p 224 none) = d257 p := by
  change (if p 163 then d2240 (change p 224 none) else d2372 (change p 224 none)) = d257 p
  rw [sub10136, sub10280]
  rfl
theorem sub10404 (p : Pattern) : d2493 (change p 224 none) = d258 p := by
  change (if p 162 then d12 (change p 224 none) else d2492 (change p 224 none)) = d258 p
  rw [sub10059, sub10403]
  rfl
theorem sub10405 (p : Pattern) : d2494 (change p 224 none) = d259 p := by
  change (if p 161 then d12 (change p 224 none) else d2493 (change p 224 none)) = d259 p
  rw [sub10059, sub10404]
  rfl
theorem sub10406 (p : Pattern) : d2495 (change p 224 none) = d260 p := by
  change (if p 160 then d2494 (change p 224 none) else d2491 (change p 224 none)) = d260 p
  rw [sub10405, sub10402]
  rfl
theorem sub10407 (p : Pattern) : d2496 (change p 224 none) = d261 p := by
  change (if p 141 then d2484 (change p 224 none) else d2495 (change p 224 none)) = d261 p
  rw [sub10395, sub10406]
  rfl
theorem sub10408 (p : Pattern) : d2497 (change p 224 none) = d262 p := by
  change (if p 138 then d12 (change p 224 none) else d2496 (change p 224 none)) = d262 p
  rw [sub10059, sub10407]
  rfl
theorem sub10409 (p : Pattern) : d2498 (change p 224 none) = d263 p := by
  change (if p 116 then d2497 (change p 224 none) else d2486 (change p 224 none)) = d263 p
  rw [sub10408, sub10397]
  rfl
theorem sub10410 (p : Pattern) : d2499 (change p 224 none) = d264 p := by
  change (if p 115 then d2498 (change p 224 none) else d2460 (change p 224 none)) = d264 p
  rw [sub10409, sub10371]
  rfl
theorem sub10411 (p : Pattern) : d2500 (change p 224 none) = d265 p := by
  change (if p 71 then d2499 (change p 224 none) else d2296 (change p 224 none)) = d265 p
  rw [sub10410, sub10192]
  rfl
theorem sub10412 (p : Pattern) : d2501 (change p 224 none) = d266 p := by
  change (if p 49 then d2500 (change p 224 none) else d2443 (change p 224 none)) = d266 p
  rw [sub10411, sub10354]
  rfl
theorem sub10413 (p : Pattern) : d2502 (change p 224 none) = d267 p := by
  change (if p 48 then d2501 (change p 224 none) else d2403 (change p 224 none)) = d267 p
  rw [sub10412, sub10311]
  rfl
theorem sub10414 (p : Pattern) : d0 (change p 204 (some 182)) = d0 p := by
  rfl
theorem sub10415 (p : Pattern) : d12 (change p 204 (some 182)) = d12 p := by
  rfl
theorem sub10416 (p : Pattern) : d13 (change p 204 (some 182)) = d13 p := by
  change (if p 247 then d12 (change p 204 (some 182)) else d0 (change p 204 (some 182))) = d13 p
  rw [sub10415, sub10414]
  rfl
theorem sub10417 (p : Pattern) : d14 (change p 204 (some 182)) = d14 p := by
  change (if p 246 then d13 (change p 204 (some 182)) else d0 (change p 204 (some 182))) = d14 p
  rw [sub10416, sub10414]
  rfl
theorem sub10418 (p : Pattern) : d2 (change p 204 (some 182)) = d2 p := by
  rfl
theorem sub10419 (p : Pattern) : d1683 (change p 204 (some 182)) = d1683 p := by
  change (if p 247 then d2 (change p 204 (some 182)) else d0 (change p 204 (some 182))) = d1683 p
  rw [sub10418, sub10414]
  rfl
theorem sub10420 (p : Pattern) : d30 (change p 204 (some 182)) = d30 p := by
  change (if p 247 then d12 (change p 204 (some 182)) else d2 (change p 204 (some 182))) = d30 p
  rw [sub10415, sub10418]
  rfl
theorem sub10421 (p : Pattern) : d1684 (change p 204 (some 182)) = d1684 p := by
  change (if p 246 then d30 (change p 204 (some 182)) else d1683 (change p 204 (some 182))) = d1684 p
  rw [sub10420, sub10419]
  rfl
theorem sub10422 (p : Pattern) : d1685 (change p 204 (some 182)) = d1685 p := by
  change (if p 225 then d1684 (change p 204 (some 182)) else d14 (change p 204 (some 182))) = d1685 p
  rw [sub10421, sub10417]
  rfl
theorem sub10423 (p : Pattern) : d1686 (change p 204 (some 182)) = d1686 p := by
  change (if p 224 then d1684 (change p 204 (some 182)) else d1685 (change p 204 (some 182))) = d1686 p
  rw [sub10421, sub10422]
  rfl
theorem sub10424 (p : Pattern) : d1687 (change p 204 (some 182)) = d1686 p := by
  change d1686 (change p 204 (some 182)) = d1686 p
  exact sub10423 p
theorem sub10425 (p : Pattern) : d1688 (change p 204 (some 182)) = d1686 p := by
  change d1687 (change p 204 (some 182)) = d1686 p
  exact sub10424 p
theorem sub10426 (p : Pattern) : d1690 (change p 204 (some 182)) = d1686 p := by
  change d1687 (change p 204 (some 182)) = d1686 p
  exact sub10424 p
theorem sub10427 (p : Pattern) : d1691 (change p 204 (some 182)) = d1686 p := by
  change (if p 163 then d1690 (change p 204 (some 182)) else d1688 (change p 204 (some 182))) = d1686 p
  rw [sub10426, sub10425]
  simp only [ite_self]
theorem sub10428 (p : Pattern) : d1692 (change p 204 (some 182)) = d1686 p := by
  change d1687 (change p 204 (some 182)) = d1686 p
  exact sub10424 p
theorem sub10429 (p : Pattern) : d4 (change p 204 (some 182)) = d4 p := by
  rfl
theorem sub10430 (p : Pattern) : d17 (change p 204 (some 182)) = d17 p := by
  change (if p 247 then d12 (change p 204 (some 182)) else d4 (change p 204 (some 182))) = d17 p
  rw [sub10415, sub10429]
  rfl
theorem sub10431 (p : Pattern) : d18 (change p 204 (some 182)) = d18 p := by
  change (if p 246 then d17 (change p 204 (some 182)) else d4 (change p 204 (some 182))) = d18 p
  rw [sub10430, sub10429]
  rfl
theorem sub10432 (p : Pattern) : d6 (change p 204 (some 182)) = d6 p := by
  rfl
theorem sub10433 (p : Pattern) : d1693 (change p 204 (some 182)) = d1693 p := by
  change (if p 247 then d6 (change p 204 (some 182)) else d4 (change p 204 (some 182))) = d1693 p
  rw [sub10432, sub10429]
  rfl
theorem sub10434 (p : Pattern) : d34 (change p 204 (some 182)) = d34 p := by
  change (if p 247 then d12 (change p 204 (some 182)) else d6 (change p 204 (some 182))) = d34 p
  rw [sub10415, sub10432]
  rfl
theorem sub10435 (p : Pattern) : d1694 (change p 204 (some 182)) = d1694 p := by
  change (if p 246 then d34 (change p 204 (some 182)) else d1693 (change p 204 (some 182))) = d1694 p
  rw [sub10434, sub10433]
  rfl
theorem sub10436 (p : Pattern) : d1695 (change p 204 (some 182)) = d1695 p := by
  change (if p 225 then d1694 (change p 204 (some 182)) else d18 (change p 204 (some 182))) = d1695 p
  rw [sub10435, sub10431]
  rfl
theorem sub10437 (p : Pattern) : d1696 (change p 204 (some 182)) = d1696 p := by
  change (if p 224 then d1694 (change p 204 (some 182)) else d1695 (change p 204 (some 182))) = d1696 p
  rw [sub10435, sub10436]
  rfl
theorem sub10438 (p : Pattern) : d1697 (change p 204 (some 182)) = d1696 p := by
  change d1696 (change p 204 (some 182)) = d1696 p
  exact sub10437 p
theorem sub10439 (p : Pattern) : d1698 (change p 204 (some 182)) = d1696 p := by
  change d1697 (change p 204 (some 182)) = d1696 p
  exact sub10438 p
end NetHack.Sokoban22Refined85
