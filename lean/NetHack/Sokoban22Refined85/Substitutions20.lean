/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions19
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2400 (p : Pattern) : d298 (change p 10000 (some 141)) = d298 p := by
  change (if p 182 then d108 (change p 10000 (some 141)) else d282 (change p 10000 (some 141))) = d298 p
  rw [sub2334, sub2388]
  rfl
theorem sub2401 (p : Pattern) : d299 (change p 10000 (some 141)) = d299 p := by
  change (if p 163 then d298 (change p 10000 (some 141)) else d269 (change p 10000 (some 141))) = d299 p
  rw [sub2400, sub2399]
  rfl
theorem sub2402 (p : Pattern) : d292 (change p 10000 (some 141)) = d292 p := by
  change (if p 182 then d121 (change p 10000 (some 141)) else d273 (change p 10000 (some 141))) = d292 p
  rw [sub2344, sub2391]
  rfl
theorem sub2403 (p : Pattern) : d300 (change p 10000 (some 141)) = d300 p := by
  change (if p 163 then d12 (change p 10000 (some 141)) else d292 (change p 10000 (some 141))) = d300 p
  rw [sub2248, sub2402]
  rfl
theorem sub2404 (p : Pattern) : d301 (change p 10000 (some 141)) = d301 p := by
  change (if p 162 then d300 (change p 10000 (some 141)) else d299 (change p 10000 (some 141))) = d301 p
  rw [sub2403, sub2401]
  rfl
theorem sub2405 (p : Pattern) : d302 (change p 10000 (some 141)) = d302 p := by
  change (if p 162 then d12 (change p 10000 (some 141)) else d300 (change p 10000 (some 141))) = d302 p
  rw [sub2248, sub2403]
  rfl
theorem sub2406 (p : Pattern) : d303 (change p 10000 (some 141)) = d303 p := by
  change (if p 161 then d302 (change p 10000 (some 141)) else d301 (change p 10000 (some 141))) = d303 p
  rw [sub2405, sub2404]
  rfl
theorem sub2407 (p : Pattern) : d304 (change p 10000 (some 141)) = d304 p := by
  change (if p 160 then d155 (change p 10000 (some 141)) else d303 (change p 10000 (some 141))) = d304 p
  rw [sub2359, sub2406]
  rfl
theorem sub2408 (p : Pattern) : d305 (change p 10000 (some 141)) = d304 p := by
  change d304 (change p 10000 (some 141)) = d304 p
  exact sub2407 p
theorem sub2409 (p : Pattern) : d306 (change p 10000 (some 141)) = d4092 p := by
  change (if p 138 then d305 (change p 10000 (some 141)) else d290 (change p 10000 (some 141))) = d4092 p
  rw [sub2408, sub2398]
  rfl
theorem sub2410 (p : Pattern) : d307 (change p 10000 (some 141)) = d4093 p := by
  change (if p 138 then d12 (change p 10000 (some 141)) else d305 (change p 10000 (some 141))) = d4093 p
  rw [sub2248, sub2408]
  rfl
theorem sub2411 (p : Pattern) : d308 (change p 10000 (some 141)) = d4094 p := by
  change (if p 116 then d307 (change p 10000 (some 141)) else d306 (change p 10000 (some 141))) = d4094 p
  rw [sub2410, sub2409]
  rfl
theorem sub2412 (p : Pattern) : d309 (change p 10000 (some 141)) = d4095 p := by
  change (if p 115 then d308 (change p 10000 (some 141)) else d225 (change p 10000 (some 141))) = d4095 p
  rw [sub2411, sub2385]
  rfl
theorem sub2413 (p : Pattern) : d310 (change p 10000 (some 141)) = d4096 p := by
  change (if p 71 then d309 (change p 10000 (some 141)) else d101 (change p 10000 (some 141))) = d4096 p
  rw [sub2412, sub2319]
  rfl
theorem sub2414 (p : Pattern) : d311 (change p 10000 (some 141)) = d4097 p := by
  change (if p 49 then d310 (change p 10000 (some 141)) else d101 (change p 10000 (some 141))) = d4097 p
  rw [sub2413, sub2319]
  rfl
theorem sub2415 (p : Pattern) : d312 (change p 10000 (some 141)) = d4098 p := by
  change (if p 48 then d311 (change p 10000 (some 141)) else d169 (change p 10000 (some 141))) = d4098 p
  rw [sub2414, sub2370]
  rfl
theorem sub2416 (p : Pattern) : d170 (change p 10000 (some 115)) = d170 p := by
  change (if p 182 then d36 (change p 10000 (some 115)) else d31 (change p 10000 (some 115))) = d170 p
  rw [sub1827, sub1821]
  rfl
theorem sub2417 (p : Pattern) : d171 (change p 10000 (some 115)) = d171 p := by
  change (if p 163 then d170 (change p 10000 (some 115)) else d53 (change p 10000 (some 115))) = d171 p
  rw [sub2416, sub1845]
  rfl
theorem sub2418 (p : Pattern) : d172 (change p 10000 (some 115)) = d172 p := by
  change (if p 182 then d41 (change p 10000 (some 115)) else d31 (change p 10000 (some 115))) = d172 p
  rw [sub1833, sub1821]
  rfl
theorem sub2419 (p : Pattern) : d173 (change p 10000 (some 115)) = d173 p := by
  change (if p 182 then d12 (change p 10000 (some 115)) else d35 (change p 10000 (some 115))) = d173 p
  rw [sub1799, sub1826]
  rfl
theorem sub2420 (p : Pattern) : d174 (change p 10000 (some 115)) = d174 p := by
  change (if p 163 then d173 (change p 10000 (some 115)) else d172 (change p 10000 (some 115))) = d174 p
  rw [sub2419, sub2418]
  rfl
theorem sub2421 (p : Pattern) : d175 (change p 10000 (some 115)) = d175 p := by
  change (if p 162 then d174 (change p 10000 (some 115)) else d171 (change p 10000 (some 115))) = d175 p
  rw [sub2420, sub2417]
  rfl
theorem sub2422 (p : Pattern) : d176 (change p 10000 (some 115)) = d176 p := by
  change (if p 163 then d173 (change p 10000 (some 115)) else d66 (change p 10000 (some 115))) = d176 p
  rw [sub2419, sub1859]
  rfl
theorem sub2423 (p : Pattern) : d177 (change p 10000 (some 115)) = d177 p := by
  change (if p 162 then d73 (change p 10000 (some 115)) else d176 (change p 10000 (some 115))) = d177 p
  rw [sub1866, sub2422]
  rfl
theorem sub2424 (p : Pattern) : d178 (change p 10000 (some 115)) = d178 p := by
  change (if p 161 then d177 (change p 10000 (some 115)) else d175 (change p 10000 (some 115))) = d178 p
  rw [sub2423, sub2421]
  rfl
theorem sub2425 (p : Pattern) : d179 (change p 10000 (some 115)) = d179 p := by
  change (if p 160 then d178 (change p 10000 (some 115)) else d29 (change p 10000 (some 115))) = d179 p
  rw [sub2424, sub1818]
  rfl
theorem sub2426 (p : Pattern) : d180 (change p 10000 (some 115)) = d180 p := by
  change (if p 163 then d43 (change p 10000 (some 115)) else d170 (change p 10000 (some 115))) = d180 p
  rw [sub1835, sub2416]
  rfl
theorem sub2427 (p : Pattern) : d181 (change p 10000 (some 115)) = d181 p := by
  change (if p 163 then d72 (change p 10000 (some 115)) else d173 (change p 10000 (some 115))) = d181 p
  rw [sub1865, sub2419]
  rfl
theorem sub2428 (p : Pattern) : d182 (change p 10000 (some 115)) = d182 p := by
  change (if p 162 then d181 (change p 10000 (some 115)) else d180 (change p 10000 (some 115))) = d182 p
  rw [sub2427, sub2426]
  rfl
theorem sub2429 (p : Pattern) : d183 (change p 10000 (some 115)) = d183 p := by
  change (if p 163 then d12 (change p 10000 (some 115)) else d173 (change p 10000 (some 115))) = d183 p
  rw [sub1799, sub2419]
  rfl
theorem sub2430 (p : Pattern) : d184 (change p 10000 (some 115)) = d184 p := by
  change (if p 162 then d12 (change p 10000 (some 115)) else d183 (change p 10000 (some 115))) = d184 p
  rw [sub1799, sub2429]
  rfl
theorem sub2431 (p : Pattern) : d185 (change p 10000 (some 115)) = d185 p := by
  change (if p 161 then d184 (change p 10000 (some 115)) else d182 (change p 10000 (some 115))) = d185 p
  rw [sub2430, sub2428]
  rfl
theorem sub2432 (p : Pattern) : d186 (change p 10000 (some 115)) = d186 p := by
  change (if p 160 then d185 (change p 10000 (some 115)) else d65 (change p 10000 (some 115))) = d186 p
  rw [sub2431, sub1858]
  rfl
theorem sub2433 (p : Pattern) : d187 (change p 10000 (some 115)) = d187 p := by
  change (if p 141 then d186 (change p 10000 (some 115)) else d179 (change p 10000 (some 115))) = d187 p
  rw [sub2432, sub2425]
  rfl
theorem sub2434 (p : Pattern) : d188 (change p 10000 (some 115)) = d188 p := by
  change (if p 162 then d79 (change p 10000 (some 115)) else d16 (change p 10000 (some 115))) = d188 p
  rw [sub1872, sub1803]
  rfl
theorem sub2435 (p : Pattern) : d189 (change p 10000 (some 115)) = d189 p := by
  change (if p 161 then d80 (change p 10000 (some 115)) else d188 (change p 10000 (some 115))) = d189 p
  rw [sub1873, sub2434]
  rfl
theorem sub2436 (p : Pattern) : d8 (change p 10000 (some 115)) = d8 p := by
  rfl
theorem sub2437 (p : Pattern) : d190 (change p 10000 (some 115)) = d190 p := by
  change (if p 247 then d12 (change p 10000 (some 115)) else d8 (change p 10000 (some 115))) = d190 p
  rw [sub1799, sub2436]
  rfl
theorem sub2438 (p : Pattern) : d191 (change p 10000 (some 115)) = d191 p := by
  change (if p 246 then d190 (change p 10000 (some 115)) else d8 (change p 10000 (some 115))) = d191 p
  rw [sub2437, sub2436]
  rfl
theorem sub2439 (p : Pattern) : d192 (change p 10000 (some 115)) = d192 p := by
  change (if p 204 then d12 (change p 10000 (some 115)) else d191 (change p 10000 (some 115))) = d192 p
  rw [sub1799, sub2438]
  rfl
theorem sub2440 (p : Pattern) : d193 (change p 10000 (some 115)) = d193 p := by
  change (if p 182 then d192 (change p 10000 (some 115)) else d191 (change p 10000 (some 115))) = d193 p
  rw [sub2439, sub2438]
  rfl
theorem sub2441 (p : Pattern) : d194 (change p 10000 (some 115)) = d194 p := by
  change (if p 163 then d193 (change p 10000 (some 115)) else d20 (change p 10000 (some 115))) = d194 p
  rw [sub2440, sub1808]
  rfl
theorem sub2442 (p : Pattern) : d195 (change p 10000 (some 115)) = d195 p := by
  change (if p 162 then d12 (change p 10000 (some 115)) else d194 (change p 10000 (some 115))) = d195 p
  rw [sub1799, sub2441]
  rfl
theorem sub2443 (p : Pattern) : d196 (change p 10000 (some 115)) = d196 p := by
  change (if p 161 then d12 (change p 10000 (some 115)) else d195 (change p 10000 (some 115))) = d196 p
  rw [sub1799, sub2442]
  rfl
theorem sub2444 (p : Pattern) : d197 (change p 10000 (some 115)) = d197 p := by
  change (if p 160 then d196 (change p 10000 (some 115)) else d189 (change p 10000 (some 115))) = d197 p
  rw [sub2443, sub2435]
  rfl
theorem sub2445 (p : Pattern) : d198 (change p 10000 (some 115)) = d198 p := by
  change (if p 163 then d62 (change p 10000 (some 115)) else d20 (change p 10000 (some 115))) = d198 p
  rw [sub1855, sub1808]
  rfl
theorem sub2446 (p : Pattern) : d199 (change p 10000 (some 115)) = d199 p := by
  change (if p 162 then d198 (change p 10000 (some 115)) else d53 (change p 10000 (some 115))) = d199 p
  rw [sub2445, sub1845]
  rfl
theorem sub2447 (p : Pattern) : d200 (change p 10000 (some 115)) = d200 p := by
  change (if p 161 then d84 (change p 10000 (some 115)) else d199 (change p 10000 (some 115))) = d200 p
  rw [sub1877, sub2446]
  rfl
theorem sub2448 (p : Pattern) : d201 (change p 10000 (some 115)) = d201 p := by
  change (if p 163 then d12 (change p 10000 (some 115)) else d193 (change p 10000 (some 115))) = d201 p
  rw [sub1799, sub2440]
  rfl
theorem sub2449 (p : Pattern) : d202 (change p 10000 (some 115)) = d202 p := by
  change (if p 162 then d12 (change p 10000 (some 115)) else d201 (change p 10000 (some 115))) = d202 p
  rw [sub1799, sub2448]
  rfl
theorem sub2450 (p : Pattern) : d203 (change p 10000 (some 115)) = d203 p := by
  change (if p 161 then d12 (change p 10000 (some 115)) else d202 (change p 10000 (some 115))) = d203 p
  rw [sub1799, sub2449]
  rfl
theorem sub2451 (p : Pattern) : d204 (change p 10000 (some 115)) = d204 p := by
  change (if p 160 then d203 (change p 10000 (some 115)) else d200 (change p 10000 (some 115))) = d204 p
  rw [sub2450, sub2447]
  rfl
theorem sub2452 (p : Pattern) : d205 (change p 10000 (some 115)) = d205 p := by
  change (if p 141 then d204 (change p 10000 (some 115)) else d197 (change p 10000 (some 115))) = d205 p
  rw [sub2451, sub2444]
  rfl
theorem sub2453 (p : Pattern) : d206 (change p 10000 (some 115)) = d206 p := by
  change (if p 138 then d205 (change p 10000 (some 115)) else d187 (change p 10000 (some 115))) = d206 p
  rw [sub2452, sub2433]
  rfl
theorem sub2454 (p : Pattern) : d207 (change p 10000 (some 115)) = d207 p := by
  change (if p 138 then d12 (change p 10000 (some 115)) else d205 (change p 10000 (some 115))) = d207 p
  rw [sub1799, sub2452]
  rfl
theorem sub2455 (p : Pattern) : d208 (change p 10000 (some 115)) = d208 p := by
  change (if p 116 then d207 (change p 10000 (some 115)) else d206 (change p 10000 (some 115))) = d208 p
  rw [sub2454, sub2453]
  rfl
theorem sub2456 (p : Pattern) : d209 (change p 10000 (some 115)) = d208 p := by
  change d208 (change p 10000 (some 115)) = d208 p
  exact sub2455 p
theorem sub2457 (p : Pattern) : d210 (change p 10000 (some 115)) = d4099 p := by
  change (if p 71 then d209 (change p 10000 (some 115)) else d101 (change p 10000 (some 115))) = d4099 p
  rw [sub2456, sub1884]
  rfl
theorem sub2458 (p : Pattern) : d226 (change p 10000 (some 115)) = d226 p := by
  change (if p 182 then d121 (change p 10000 (some 115)) else d116 (change p 10000 (some 115))) = d226 p
  rw [sub1908, sub1902]
  rfl
theorem sub2459 (p : Pattern) : d227 (change p 10000 (some 115)) = d227 p := by
  change (if p 163 then d226 (change p 10000 (some 115)) else d132 (change p 10000 (some 115))) = d227 p
  rw [sub2458, sub1919]
  rfl
theorem sub2460 (p : Pattern) : d215 (change p 10000 (some 115)) = d215 p := by
  change (if p 163 then d12 (change p 10000 (some 115)) else d125 (change p 10000 (some 115))) = d215 p
  rw [sub1799, sub1912]
  rfl
theorem sub2461 (p : Pattern) : d228 (change p 10000 (some 115)) = d228 p := by
  change (if p 162 then d215 (change p 10000 (some 115)) else d227 (change p 10000 (some 115))) = d228 p
  rw [sub2460, sub2459]
  rfl
theorem sub2462 (p : Pattern) : d229 (change p 10000 (some 115)) = d229 p := by
  change (if p 182 then d12 (change p 10000 (some 115)) else d120 (change p 10000 (some 115))) = d229 p
  rw [sub1799, sub1907]
  rfl
theorem sub2463 (p : Pattern) : d230 (change p 10000 (some 115)) = d230 p := by
  change (if p 163 then d12 (change p 10000 (some 115)) else d229 (change p 10000 (some 115))) = d230 p
  rw [sub1799, sub2462]
  rfl
theorem sub2464 (p : Pattern) : d231 (change p 10000 (some 115)) = d231 p := by
  change (if p 162 then d12 (change p 10000 (some 115)) else d230 (change p 10000 (some 115))) = d231 p
  rw [sub1799, sub2463]
  rfl
theorem sub2465 (p : Pattern) : d232 (change p 10000 (some 115)) = d232 p := by
  change (if p 161 then d231 (change p 10000 (some 115)) else d228 (change p 10000 (some 115))) = d232 p
  rw [sub2464, sub2461]
  rfl
theorem sub2466 (p : Pattern) : d233 (change p 10000 (some 115)) = d233 p := by
  change (if p 160 then d232 (change p 10000 (some 115)) else d114 (change p 10000 (some 115))) = d233 p
  rw [sub2465, sub1899]
  rfl
theorem sub2467 (p : Pattern) : d234 (change p 10000 (some 115)) = d234 p := by
  change (if p 182 then d121 (change p 10000 (some 115)) else d107 (change p 10000 (some 115))) = d234 p
  rw [sub1908, sub1892]
  rfl
theorem sub2468 (p : Pattern) : d235 (change p 10000 (some 115)) = d235 p := by
  change (if p 163 then d125 (change p 10000 (some 115)) else d234 (change p 10000 (some 115))) = d235 p
  rw [sub1912, sub2467]
  rfl
theorem sub2469 (p : Pattern) : d236 (change p 10000 (some 115)) = d236 p := by
  change (if p 162 then d230 (change p 10000 (some 115)) else d235 (change p 10000 (some 115))) = d236 p
  rw [sub2463, sub2468]
  rfl
theorem sub2470 (p : Pattern) : d237 (change p 10000 (some 115)) = d237 p := by
  change (if p 162 then d12 (change p 10000 (some 115)) else d49 (change p 10000 (some 115))) = d237 p
  rw [sub1799, sub1841]
  rfl
theorem sub2471 (p : Pattern) : d238 (change p 10000 (some 115)) = d238 p := by
  change (if p 161 then d237 (change p 10000 (some 115)) else d236 (change p 10000 (some 115))) = d238 p
  rw [sub2470, sub2469]
  rfl
theorem sub2472 (p : Pattern) : d239 (change p 10000 (some 115)) = d239 p := by
  change (if p 160 then d238 (change p 10000 (some 115)) else d214 (change p 10000 (some 115))) = d239 p
  rw [sub2471, sub1968]
  rfl
theorem sub2473 (p : Pattern) : d240 (change p 10000 (some 115)) = d240 p := by
  change (if p 141 then d239 (change p 10000 (some 115)) else d233 (change p 10000 (some 115))) = d240 p
  rw [sub2472, sub2466]
  rfl
theorem sub2474 (p : Pattern) : d241 (change p 10000 (some 115)) = d241 p := by
  change (if p 163 then d62 (change p 10000 (some 115)) else d132 (change p 10000 (some 115))) = d241 p
  rw [sub1855, sub1919]
  rfl
theorem sub2475 (p : Pattern) : d242 (change p 10000 (some 115)) = d242 p := by
  change (if p 162 then d241 (change p 10000 (some 115)) else d105 (change p 10000 (some 115))) = d242 p
  rw [sub2474, sub1889]
  rfl
theorem sub2476 (p : Pattern) : d243 (change p 10000 (some 115)) = d243 p := by
  change (if p 161 then d137 (change p 10000 (some 115)) else d242 (change p 10000 (some 115))) = d243 p
  rw [sub1924, sub2475]
  rfl
theorem sub2477 (p : Pattern) : d244 (change p 10000 (some 115)) = d244 p := by
  change (if p 160 then d155 (change p 10000 (some 115)) else d243 (change p 10000 (some 115))) = d244 p
  rw [sub1942, sub2476]
  rfl
theorem sub2478 (p : Pattern) : d245 (change p 10000 (some 115)) = d245 p := by
  change (if p 162 then d211 (change p 10000 (some 115)) else d132 (change p 10000 (some 115))) = d245 p
  rw [sub1965, sub1919]
  rfl
theorem sub2479 (p : Pattern) : d246 (change p 10000 (some 115)) = d246 p := by
  change (if p 161 then d154 (change p 10000 (some 115)) else d245 (change p 10000 (some 115))) = d246 p
  rw [sub1941, sub2478]
  rfl
theorem sub2480 (p : Pattern) : d247 (change p 10000 (some 115)) = d247 p := by
  change (if p 162 then d12 (change p 10000 (some 115)) else d27 (change p 10000 (some 115))) = d247 p
  rw [sub1799, sub1816]
  rfl
theorem sub2481 (p : Pattern) : d248 (change p 10000 (some 115)) = d248 p := by
  change (if p 161 then d12 (change p 10000 (some 115)) else d247 (change p 10000 (some 115))) = d248 p
  rw [sub1799, sub2480]
  rfl
theorem sub2482 (p : Pattern) : d249 (change p 10000 (some 115)) = d249 p := by
  change (if p 160 then d248 (change p 10000 (some 115)) else d246 (change p 10000 (some 115))) = d249 p
  rw [sub2481, sub2479]
  rfl
theorem sub2483 (p : Pattern) : d250 (change p 10000 (some 115)) = d250 p := by
  change (if p 141 then d249 (change p 10000 (some 115)) else d244 (change p 10000 (some 115))) = d250 p
  rw [sub2482, sub2477]
  rfl
theorem sub2484 (p : Pattern) : d251 (change p 10000 (some 115)) = d251 p := by
  change (if p 138 then d250 (change p 10000 (some 115)) else d240 (change p 10000 (some 115))) = d251 p
  rw [sub2483, sub2473]
  rfl
theorem sub2485 (p : Pattern) : d252 (change p 10000 (some 115)) = d252 p := by
  change (if p 163 then d26 (change p 10000 (some 115)) else d132 (change p 10000 (some 115))) = d252 p
  rw [sub1815, sub1919]
  rfl
theorem sub2486 (p : Pattern) : d253 (change p 10000 (some 115)) = d253 p := by
  change (if p 162 then d252 (change p 10000 (some 115)) else d105 (change p 10000 (some 115))) = d253 p
  rw [sub2485, sub1889]
  rfl
theorem sub2487 (p : Pattern) : d254 (change p 10000 (some 115)) = d254 p := by
  change (if p 163 then d26 (change p 10000 (some 115)) else d109 (change p 10000 (some 115))) = d254 p
  rw [sub1815, sub1894]
  rfl
theorem sub2488 (p : Pattern) : d255 (change p 10000 (some 115)) = d255 p := by
  change (if p 162 then d12 (change p 10000 (some 115)) else d254 (change p 10000 (some 115))) = d255 p
  rw [sub1799, sub2487]
  rfl
theorem sub2489 (p : Pattern) : d256 (change p 10000 (some 115)) = d256 p := by
  change (if p 161 then d255 (change p 10000 (some 115)) else d253 (change p 10000 (some 115))) = d256 p
  rw [sub2488, sub2486]
  rfl
theorem sub2490 (p : Pattern) : d257 (change p 10000 (some 115)) = d257 p := by
  change (if p 163 then d62 (change p 10000 (some 115)) else d148 (change p 10000 (some 115))) = d257 p
  rw [sub1855, sub1935]
  rfl
theorem sub2491 (p : Pattern) : d258 (change p 10000 (some 115)) = d258 p := by
  change (if p 162 then d12 (change p 10000 (some 115)) else d257 (change p 10000 (some 115))) = d258 p
  rw [sub1799, sub2490]
  rfl
theorem sub2492 (p : Pattern) : d259 (change p 10000 (some 115)) = d259 p := by
  change (if p 161 then d12 (change p 10000 (some 115)) else d258 (change p 10000 (some 115))) = d259 p
  rw [sub1799, sub2491]
  rfl
theorem sub2493 (p : Pattern) : d260 (change p 10000 (some 115)) = d260 p := by
  change (if p 160 then d259 (change p 10000 (some 115)) else d256 (change p 10000 (some 115))) = d260 p
  rw [sub2492, sub2489]
  rfl
theorem sub2494 (p : Pattern) : d261 (change p 10000 (some 115)) = d261 p := by
  change (if p 141 then d249 (change p 10000 (some 115)) else d260 (change p 10000 (some 115))) = d261 p
  rw [sub2482, sub2493]
  rfl
theorem sub2495 (p : Pattern) : d262 (change p 10000 (some 115)) = d262 p := by
  change (if p 138 then d12 (change p 10000 (some 115)) else d261 (change p 10000 (some 115))) = d262 p
  rw [sub1799, sub2494]
  rfl
theorem sub2496 (p : Pattern) : d263 (change p 10000 (some 115)) = d263 p := by
  change (if p 116 then d262 (change p 10000 (some 115)) else d251 (change p 10000 (some 115))) = d263 p
  rw [sub2495, sub2484]
  rfl
theorem sub2497 (p : Pattern) : d264 (change p 10000 (some 115)) = d263 p := by
  change d263 (change p 10000 (some 115)) = d263 p
  exact sub2496 p
theorem sub2498 (p : Pattern) : d265 (change p 10000 (some 115)) = d4100 p := by
  change (if p 71 then d264 (change p 10000 (some 115)) else d101 (change p 10000 (some 115))) = d4100 p
  rw [sub2497, sub1884]
  rfl
theorem sub2499 (p : Pattern) : d266 (change p 10000 (some 115)) = d4101 p := by
  change (if p 49 then d265 (change p 10000 (some 115)) else d210 (change p 10000 (some 115))) = d4101 p
  rw [sub2498, sub2457]
  rfl
theorem sub2500 (p : Pattern) : d267 (change p 10000 (some 115)) = d4102 p := by
  change (if p 48 then d266 (change p 10000 (some 115)) else d169 (change p 10000 (some 115))) = d4102 p
  rw [sub2499, sub1950]
  rfl
theorem sub2501 (p : Pattern) : d0 (change p 115 (some 116)) = d0 p := by
  rfl
theorem sub2502 (p : Pattern) : d12 (change p 115 (some 116)) = d12 p := by
  rfl
theorem sub2503 (p : Pattern) : d13 (change p 115 (some 116)) = d13 p := by
  change (if p 247 then d12 (change p 115 (some 116)) else d0 (change p 115 (some 116))) = d13 p
  rw [sub2502, sub2501]
  rfl
theorem sub2504 (p : Pattern) : d14 (change p 115 (some 116)) = d14 p := by
  change (if p 246 then d13 (change p 115 (some 116)) else d0 (change p 115 (some 116))) = d14 p
  rw [sub2503, sub2501]
  rfl
theorem sub2505 (p : Pattern) : d15 (change p 115 (some 116)) = d15 p := by
  change (if p 204 then d12 (change p 115 (some 116)) else d14 (change p 115 (some 116))) = d15 p
  rw [sub2502, sub2504]
  rfl
theorem sub2506 (p : Pattern) : d16 (change p 115 (some 116)) = d16 p := by
  change (if p 182 then d15 (change p 115 (some 116)) else d14 (change p 115 (some 116))) = d16 p
  rw [sub2505, sub2504]
  rfl
theorem sub2507 (p : Pattern) : d4 (change p 115 (some 116)) = d4 p := by
  rfl
theorem sub2508 (p : Pattern) : d17 (change p 115 (some 116)) = d17 p := by
  change (if p 247 then d12 (change p 115 (some 116)) else d4 (change p 115 (some 116))) = d17 p
  rw [sub2502, sub2507]
  rfl
theorem sub2509 (p : Pattern) : d18 (change p 115 (some 116)) = d18 p := by
  change (if p 246 then d17 (change p 115 (some 116)) else d4 (change p 115 (some 116))) = d18 p
  rw [sub2508, sub2507]
  rfl
theorem sub2510 (p : Pattern) : d19 (change p 115 (some 116)) = d19 p := by
  change (if p 204 then d12 (change p 115 (some 116)) else d18 (change p 115 (some 116))) = d19 p
  rw [sub2502, sub2509]
  rfl
theorem sub2511 (p : Pattern) : d20 (change p 115 (some 116)) = d20 p := by
  change (if p 182 then d19 (change p 115 (some 116)) else d18 (change p 115 (some 116))) = d20 p
  rw [sub2510, sub2509]
  rfl
theorem sub2512 (p : Pattern) : d21 (change p 115 (some 116)) = d21 p := by
  change (if p 163 then d20 (change p 115 (some 116)) else d16 (change p 115 (some 116))) = d21 p
  rw [sub2511, sub2506]
  rfl
theorem sub2513 (p : Pattern) : d22 (change p 115 (some 116)) = d22 p := by
  change (if p 162 then d21 (change p 115 (some 116)) else d16 (change p 115 (some 116))) = d22 p
  rw [sub2512, sub2506]
  rfl
theorem sub2514 (p : Pattern) : d9 (change p 115 (some 116)) = d9 p := by
  rfl
theorem sub2515 (p : Pattern) : d23 (change p 115 (some 116)) = d23 p := by
  change (if p 247 then d12 (change p 115 (some 116)) else d9 (change p 115 (some 116))) = d23 p
  rw [sub2502, sub2514]
  rfl
theorem sub2516 (p : Pattern) : d24 (change p 115 (some 116)) = d24 p := by
  change (if p 246 then d23 (change p 115 (some 116)) else d9 (change p 115 (some 116))) = d24 p
  rw [sub2515, sub2514]
  rfl
theorem sub2517 (p : Pattern) : d25 (change p 115 (some 116)) = d25 p := by
  change (if p 204 then d12 (change p 115 (some 116)) else d24 (change p 115 (some 116))) = d25 p
  rw [sub2502, sub2516]
  rfl
theorem sub2518 (p : Pattern) : d26 (change p 115 (some 116)) = d26 p := by
  change (if p 182 then d25 (change p 115 (some 116)) else d24 (change p 115 (some 116))) = d26 p
  rw [sub2517, sub2516]
  rfl
theorem sub2519 (p : Pattern) : d27 (change p 115 (some 116)) = d27 p := by
  change (if p 163 then d12 (change p 115 (some 116)) else d26 (change p 115 (some 116))) = d27 p
  rw [sub2502, sub2518]
  rfl
end NetHack.Sokoban22Refined85
