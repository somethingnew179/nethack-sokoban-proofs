/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions84
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub10200 (p : Pattern) : d2304 (change p 224 none) = d54 p := by
  change (if p 163 then d2232 (change p 224 none) else d2191 (change p 224 none)) = d54 p
  rw [sub10125, sub10069]
  rfl
theorem sub10201 (p : Pattern) : d2305 (change p 224 none) = d56 p := by
  change (if p 162 then d2234 (change p 224 none) else d2304 (change p 224 none)) = d56 p
  rw [sub10127, sub10200]
  rfl
theorem sub10202 (p : Pattern) : d2306 (change p 224 none) = d65 p := by
  change (if p 161 then d2242 (change p 224 none) else d2305 (change p 224 none)) = d65 p
  rw [sub10138, sub10201]
  rfl
theorem sub10203 (p : Pattern) : d2307 (change p 224 none) = d76 p := by
  change (if p 160 then d2253 (change p 224 none) else d2306 (change p 224 none)) = d76 p
  rw [sub10149, sub10202]
  rfl
theorem sub10204 (p : Pattern) : d2308 (change p 224 none) = d77 p := by
  change (if p 141 then d2307 (change p 224 none) else d2303 (change p 224 none)) = d77 p
  rw [sub10203, sub10199]
  rfl
theorem sub10205 (p : Pattern) : d2309 (change p 224 none) = d88 p := by
  change (if p 138 then d2270 (change p 224 none) else d2308 (change p 224 none)) = d88 p
  rw [sub10166, sub10204]
  rfl
theorem sub10206 (p : Pattern) : d2310 (change p 224 none) = d97 p := by
  change (if p 138 then d2284 (change p 224 none) else d2270 (change p 224 none)) = d97 p
  rw [sub10180, sub10166]
  rfl
theorem sub10207 (p : Pattern) : d2311 (change p 224 none) = d98 p := by
  change (if p 116 then d2310 (change p 224 none) else d2309 (change p 224 none)) = d98 p
  rw [sub10206, sub10205]
  rfl
theorem sub10208 (p : Pattern) : d2312 (change p 224 none) = d52 p := by
  change (if p 160 then d2227 (change p 224 none) else d2274 (change p 224 none)) = d52 p
  rw [sub10120, sub10170]
  rfl
theorem sub10209 (p : Pattern) : d2313 (change p 224 none) = d77 p := by
  change (if p 141 then d2291 (change p 224 none) else d2312 (change p 224 none)) = d77 p
  rw [sub10187, sub10208]
  rfl
theorem sub10210 (p : Pattern) : d2314 (change p 224 none) = d88 p := by
  change (if p 138 then d2270 (change p 224 none) else d2313 (change p 224 none)) = d88 p
  rw [sub10166, sub10209]
  rfl
theorem sub10211 (p : Pattern) : d2315 (change p 224 none) = d100 p := by
  change (if p 116 then d2294 (change p 224 none) else d2314 (change p 224 none)) = d100 p
  rw [sub10190, sub10210]
  rfl
theorem sub10212 (p : Pattern) : d2316 (change p 224 none) = d101 p := by
  change (if p 115 then d2315 (change p 224 none) else d2311 (change p 224 none)) = d101 p
  rw [sub10211, sub10207]
  rfl
theorem sub10213 (p : Pattern) : d2317 (change p 224 none) = d101 p := by
  change (if p 71 then d2316 (change p 224 none) else d2296 (change p 224 none)) = d101 p
  rw [sub10212, sub10192]
  simp only [ite_self]
theorem sub10214 (p : Pattern) : d1 (change p 224 none) = d1 p := by
  rfl
theorem sub10215 (p : Pattern) : d102 (change p 224 none) = d102 p := by
  change (if p 247 then d12 (change p 224 none) else d1 (change p 224 none)) = d102 p
  rw [sub10059, sub10214]
  rfl
theorem sub10216 (p : Pattern) : d103 (change p 224 none) = d103 p := by
  change (if p 246 then d102 (change p 224 none) else d1 (change p 224 none)) = d103 p
  rw [sub10215, sub10214]
  rfl
theorem sub10217 (p : Pattern) : d2318 (change p 224 none) = d103 p := by
  change d103 (change p 224 none) = d103 p
  exact sub10216 p
theorem sub10218 (p : Pattern) : d2319 (change p 224 none) = d103 p := by
  change d103 (change p 224 none) = d103 p
  exact sub10216 p
theorem sub10219 (p : Pattern) : d2320 (change p 224 none) = d103 p := by
  change (if p 204 then d2319 (change p 224 none) else d2318 (change p 224 none)) = d103 p
  rw [sub10218, sub10217]
  simp only [ite_self]
theorem sub10220 (p : Pattern) : d2321 (change p 224 none) = d104 p := by
  change (if p 204 then d12 (change p 224 none) else d2319 (change p 224 none)) = d104 p
  rw [sub10059, sub10218]
  rfl
theorem sub10221 (p : Pattern) : d2322 (change p 224 none) = d105 p := by
  change (if p 182 then d2321 (change p 224 none) else d2320 (change p 224 none)) = d105 p
  rw [sub10220, sub10219]
  rfl
theorem sub10222 (p : Pattern) : d2323 (change p 224 none) = d103 p := by
  change d103 (change p 224 none) = d103 p
  exact sub10216 p
theorem sub10223 (p : Pattern) : d2324 (change p 224 none) = d103 p := by
  change (if p 204 then d2319 (change p 224 none) else d2323 (change p 224 none)) = d103 p
  rw [sub10218, sub10222]
  simp only [ite_self]
theorem sub10224 (p : Pattern) : d2325 (change p 224 none) = d105 p := by
  change (if p 182 then d2321 (change p 224 none) else d2324 (change p 224 none)) = d105 p
  rw [sub10220, sub10223]
  rfl
theorem sub10225 (p : Pattern) : d2326 (change p 224 none) = d105 p := by
  change (if p 163 then d2325 (change p 224 none) else d2322 (change p 224 none)) = d105 p
  rw [sub10224, sub10221]
  simp only [ite_self]
theorem sub10226 (p : Pattern) : d2327 (change p 224 none) = d105 p := by
  change (if p 182 then d2321 (change p 224 none) else d2319 (change p 224 none)) = d105 p
  rw [sub10220, sub10218]
  rfl
theorem sub10227 (p : Pattern) : d5 (change p 224 none) = d5 p := by
  rfl
theorem sub10228 (p : Pattern) : d106 (change p 224 none) = d106 p := by
  change (if p 247 then d12 (change p 224 none) else d5 (change p 224 none)) = d106 p
  rw [sub10059, sub10227]
  rfl
theorem sub10229 (p : Pattern) : d107 (change p 224 none) = d107 p := by
  change (if p 246 then d106 (change p 224 none) else d5 (change p 224 none)) = d107 p
  rw [sub10228, sub10227]
  rfl
theorem sub10230 (p : Pattern) : d2328 (change p 224 none) = d107 p := by
  change d107 (change p 224 none) = d107 p
  exact sub10229 p
theorem sub10231 (p : Pattern) : d2329 (change p 224 none) = d108 p := by
  change (if p 204 then d12 (change p 224 none) else d2328 (change p 224 none)) = d108 p
  rw [sub10059, sub10230]
  rfl
theorem sub10232 (p : Pattern) : d2330 (change p 224 none) = d109 p := by
  change (if p 182 then d2329 (change p 224 none) else d2328 (change p 224 none)) = d109 p
  rw [sub10231, sub10230]
  rfl
theorem sub10233 (p : Pattern) : d2331 (change p 224 none) = d110 p := by
  change (if p 163 then d2330 (change p 224 none) else d2327 (change p 224 none)) = d110 p
  rw [sub10232, sub10226]
  rfl
theorem sub10234 (p : Pattern) : d2332 (change p 224 none) = d111 p := by
  change (if p 162 then d2331 (change p 224 none) else d2326 (change p 224 none)) = d111 p
  rw [sub10233, sub10225]
  rfl
theorem sub10235 (p : Pattern) : d2333 (change p 224 none) = d112 p := by
  change (if p 163 then d12 (change p 224 none) else d2238 (change p 224 none)) = d112 p
  rw [sub10059, sub10134]
  rfl
theorem sub10236 (p : Pattern) : d2334 (change p 224 none) = d113 p := by
  change (if p 162 then d2333 (change p 224 none) else d2331 (change p 224 none)) = d113 p
  rw [sub10235, sub10233]
  rfl
theorem sub10237 (p : Pattern) : d2335 (change p 224 none) = d114 p := by
  change (if p 161 then d2334 (change p 224 none) else d2332 (change p 224 none)) = d114 p
  rw [sub10236, sub10234]
  rfl
theorem sub10238 (p : Pattern) : d3 (change p 224 none) = d3 p := by
  rfl
theorem sub10239 (p : Pattern) : d115 (change p 224 none) = d115 p := by
  change (if p 247 then d12 (change p 224 none) else d3 (change p 224 none)) = d115 p
  rw [sub10059, sub10238]
  rfl
theorem sub10240 (p : Pattern) : d116 (change p 224 none) = d116 p := by
  change (if p 246 then d115 (change p 224 none) else d3 (change p 224 none)) = d116 p
  rw [sub10239, sub10238]
  rfl
theorem sub10241 (p : Pattern) : d2336 (change p 224 none) = d116 p := by
  change d116 (change p 224 none) = d116 p
  exact sub10240 p
theorem sub10242 (p : Pattern) : d2337 (change p 224 none) = d117 p := by
  change (if p 204 then d12 (change p 224 none) else d2336 (change p 224 none)) = d117 p
  rw [sub10059, sub10241]
  rfl
theorem sub10243 (p : Pattern) : d2338 (change p 224 none) = d118 p := by
  change (if p 182 then d2337 (change p 224 none) else d2319 (change p 224 none)) = d118 p
  rw [sub10242, sub10218]
  rfl
theorem sub10244 (p : Pattern) : d7 (change p 224 none) = d7 p := by
  rfl
theorem sub10245 (p : Pattern) : d119 (change p 224 none) = d119 p := by
  change (if p 247 then d12 (change p 224 none) else d7 (change p 224 none)) = d119 p
  rw [sub10059, sub10244]
  rfl
theorem sub10246 (p : Pattern) : d120 (change p 224 none) = d120 p := by
  change (if p 246 then d119 (change p 224 none) else d7 (change p 224 none)) = d120 p
  rw [sub10245, sub10244]
  rfl
theorem sub10247 (p : Pattern) : d2339 (change p 224 none) = d120 p := by
  change d120 (change p 224 none) = d120 p
  exact sub10246 p
theorem sub10248 (p : Pattern) : d2340 (change p 224 none) = d121 p := by
  change (if p 204 then d12 (change p 224 none) else d2339 (change p 224 none)) = d121 p
  rw [sub10059, sub10247]
  rfl
theorem sub10249 (p : Pattern) : d2341 (change p 224 none) = d122 p := by
  change (if p 182 then d2340 (change p 224 none) else d2319 (change p 224 none)) = d122 p
  rw [sub10248, sub10218]
  rfl
theorem sub10250 (p : Pattern) : d2342 (change p 224 none) = d123 p := by
  change (if p 163 then d2341 (change p 224 none) else d2338 (change p 224 none)) = d123 p
  rw [sub10249, sub10243]
  rfl
theorem sub10251 (p : Pattern) : d2343 (change p 224 none) = d124 p := by
  change (if p 182 then d12 (change p 224 none) else d2319 (change p 224 none)) = d124 p
  rw [sub10059, sub10218]
  rfl
theorem sub10252 (p : Pattern) : d2344 (change p 224 none) = d125 p := by
  change (if p 182 then d12 (change p 224 none) else d2328 (change p 224 none)) = d125 p
  rw [sub10059, sub10230]
  rfl
theorem sub10253 (p : Pattern) : d2345 (change p 224 none) = d126 p := by
  change (if p 163 then d2344 (change p 224 none) else d2343 (change p 224 none)) = d126 p
  rw [sub10252, sub10251]
  rfl
theorem sub10254 (p : Pattern) : d2346 (change p 224 none) = d127 p := by
  change (if p 162 then d2345 (change p 224 none) else d2342 (change p 224 none)) = d127 p
  rw [sub10253, sub10250]
  rfl
theorem sub10255 (p : Pattern) : d2347 (change p 224 none) = d128 p := by
  change (if p 163 then d12 (change p 224 none) else d2248 (change p 224 none)) = d128 p
  rw [sub10059, sub10144]
  rfl
theorem sub10256 (p : Pattern) : d2348 (change p 224 none) = d129 p := by
  change (if p 162 then d2347 (change p 224 none) else d2345 (change p 224 none)) = d129 p
  rw [sub10255, sub10253]
  rfl
theorem sub10257 (p : Pattern) : d2349 (change p 224 none) = d130 p := by
  change (if p 161 then d2348 (change p 224 none) else d2346 (change p 224 none)) = d130 p
  rw [sub10256, sub10254]
  rfl
theorem sub10258 (p : Pattern) : d2350 (change p 224 none) = d131 p := by
  change (if p 160 then d2349 (change p 224 none) else d2335 (change p 224 none)) = d131 p
  rw [sub10257, sub10237]
  rfl
theorem sub10259 (p : Pattern) : d2351 (change p 224 none) = d103 p := by
  change d103 (change p 224 none) = d103 p
  exact sub10216 p
theorem sub10260 (p : Pattern) : d2352 (change p 224 none) = d103 p := by
  change (if p 204 then d2319 (change p 224 none) else d2351 (change p 224 none)) = d103 p
  rw [sub10218, sub10259]
  simp only [ite_self]
theorem sub10261 (p : Pattern) : d2353 (change p 224 none) = d105 p := by
  change (if p 182 then d2321 (change p 224 none) else d2352 (change p 224 none)) = d105 p
  rw [sub10220, sub10260]
  rfl
theorem sub10262 (p : Pattern) : d2354 (change p 224 none) = d132 p := by
  change (if p 182 then d2337 (change p 224 none) else d2336 (change p 224 none)) = d132 p
  rw [sub10242, sub10241]
  rfl
theorem sub10263 (p : Pattern) : d2355 (change p 224 none) = d133 p := by
  change (if p 163 then d2354 (change p 224 none) else d2353 (change p 224 none)) = d133 p
  rw [sub10262, sub10261]
  rfl
theorem sub10264 (p : Pattern) : d2356 (change p 224 none) = d134 p := by
  change (if p 163 then d2238 (change p 224 none) else d2330 (change p 224 none)) = d134 p
  rw [sub10134, sub10232]
  rfl
theorem sub10265 (p : Pattern) : d2357 (change p 224 none) = d135 p := by
  change (if p 162 then d2356 (change p 224 none) else d2355 (change p 224 none)) = d135 p
  rw [sub10264, sub10263]
  rfl
theorem sub10266 (p : Pattern) : d2358 (change p 224 none) = d136 p := by
  change (if p 163 then d2240 (change p 224 none) else d2330 (change p 224 none)) = d136 p
  rw [sub10136, sub10232]
  rfl
theorem sub10267 (p : Pattern) : d2359 (change p 224 none) = d137 p := by
  change (if p 162 then d12 (change p 224 none) else d2358 (change p 224 none)) = d137 p
  rw [sub10059, sub10266]
  rfl
theorem sub10268 (p : Pattern) : d2360 (change p 224 none) = d138 p := by
  change (if p 161 then d2359 (change p 224 none) else d2357 (change p 224 none)) = d138 p
  rw [sub10267, sub10265]
  rfl
theorem sub10269 (p : Pattern) : d2361 (change p 224 none) = d139 p := by
  change (if p 182 then d12 (change p 224 none) else d2336 (change p 224 none)) = d139 p
  rw [sub10059, sub10241]
  rfl
theorem sub10270 (p : Pattern) : d2362 (change p 224 none) = d140 p := by
  change (if p 163 then d2361 (change p 224 none) else d2341 (change p 224 none)) = d140 p
  rw [sub10269, sub10249]
  rfl
theorem sub10271 (p : Pattern) : d2363 (change p 224 none) = d141 p := by
  change (if p 163 then d2248 (change p 224 none) else d2344 (change p 224 none)) = d141 p
  rw [sub10144, sub10252]
  rfl
theorem sub10272 (p : Pattern) : d2364 (change p 224 none) = d142 p := by
  change (if p 162 then d2363 (change p 224 none) else d2362 (change p 224 none)) = d142 p
  rw [sub10271, sub10270]
  rfl
theorem sub10273 (p : Pattern) : d2365 (change p 224 none) = d143 p := by
  change (if p 163 then d2250 (change p 224 none) else d2344 (change p 224 none)) = d143 p
  rw [sub10146, sub10252]
  rfl
theorem sub10274 (p : Pattern) : d2366 (change p 224 none) = d144 p := by
  change (if p 162 then d12 (change p 224 none) else d2365 (change p 224 none)) = d144 p
  rw [sub10059, sub10273]
  rfl
theorem sub10275 (p : Pattern) : d2367 (change p 224 none) = d145 p := by
  change (if p 161 then d2366 (change p 224 none) else d2364 (change p 224 none)) = d145 p
  rw [sub10274, sub10272]
  rfl
theorem sub10276 (p : Pattern) : d2368 (change p 224 none) = d146 p := by
  change (if p 160 then d2367 (change p 224 none) else d2360 (change p 224 none)) = d146 p
  rw [sub10275, sub10268]
  rfl
theorem sub10277 (p : Pattern) : d2369 (change p 224 none) = d147 p := by
  change (if p 141 then d2368 (change p 224 none) else d2350 (change p 224 none)) = d147 p
  rw [sub10276, sub10258]
  rfl
theorem sub10278 (p : Pattern) : d2370 (change p 224 none) = d111 p := by
  change (if p 162 then d2331 (change p 224 none) else d2327 (change p 224 none)) = d111 p
  rw [sub10233, sub10226]
  rfl
theorem sub10279 (p : Pattern) : d2371 (change p 224 none) = d114 p := by
  change (if p 161 then d2334 (change p 224 none) else d2370 (change p 224 none)) = d114 p
  rw [sub10236, sub10278]
  rfl
theorem sub10280 (p : Pattern) : d2372 (change p 224 none) = d148 p := by
  change (if p 182 then d2340 (change p 224 none) else d2339 (change p 224 none)) = d148 p
  rw [sub10248, sub10247]
  rfl
theorem sub10281 (p : Pattern) : d2373 (change p 224 none) = d149 p := by
  change (if p 163 then d2372 (change p 224 none) else d2354 (change p 224 none)) = d149 p
  rw [sub10280, sub10262]
  rfl
theorem sub10282 (p : Pattern) : d2374 (change p 224 none) = d150 p := by
  change (if p 162 then d12 (change p 224 none) else d2373 (change p 224 none)) = d150 p
  rw [sub10059, sub10281]
  rfl
theorem sub10283 (p : Pattern) : d2375 (change p 224 none) = d151 p := by
  change (if p 161 then d12 (change p 224 none) else d2374 (change p 224 none)) = d151 p
  rw [sub10059, sub10282]
  rfl
theorem sub10284 (p : Pattern) : d2376 (change p 224 none) = d152 p := by
  change (if p 160 then d2375 (change p 224 none) else d2371 (change p 224 none)) = d152 p
  rw [sub10283, sub10279]
  rfl
theorem sub10285 (p : Pattern) : d2377 (change p 224 none) = d133 p := by
  change (if p 163 then d2354 (change p 224 none) else d2327 (change p 224 none)) = d133 p
  rw [sub10262, sub10226]
  rfl
theorem sub10286 (p : Pattern) : d2378 (change p 224 none) = d135 p := by
  change (if p 162 then d2356 (change p 224 none) else d2377 (change p 224 none)) = d135 p
  rw [sub10264, sub10285]
  rfl
theorem sub10287 (p : Pattern) : d2379 (change p 224 none) = d138 p := by
  change (if p 161 then d2359 (change p 224 none) else d2378 (change p 224 none)) = d138 p
  rw [sub10267, sub10286]
  rfl
theorem sub10288 (p : Pattern) : d2380 (change p 224 none) = d153 p := by
  change (if p 163 then d12 (change p 224 none) else d2372 (change p 224 none)) = d153 p
  rw [sub10059, sub10280]
  rfl
theorem sub10289 (p : Pattern) : d2381 (change p 224 none) = d154 p := by
  change (if p 162 then d12 (change p 224 none) else d2380 (change p 224 none)) = d154 p
  rw [sub10059, sub10288]
  rfl
theorem sub10290 (p : Pattern) : d2382 (change p 224 none) = d155 p := by
  change (if p 161 then d12 (change p 224 none) else d2381 (change p 224 none)) = d155 p
  rw [sub10059, sub10289]
  rfl
theorem sub10291 (p : Pattern) : d2383 (change p 224 none) = d156 p := by
  change (if p 160 then d2382 (change p 224 none) else d2379 (change p 224 none)) = d156 p
  rw [sub10290, sub10287]
  rfl
theorem sub10292 (p : Pattern) : d2384 (change p 224 none) = d157 p := by
  change (if p 141 then d2383 (change p 224 none) else d2376 (change p 224 none)) = d157 p
  rw [sub10291, sub10284]
  rfl
theorem sub10293 (p : Pattern) : d2385 (change p 224 none) = d158 p := by
  change (if p 138 then d2384 (change p 224 none) else d2369 (change p 224 none)) = d158 p
  rw [sub10292, sub10277]
  rfl
theorem sub10294 (p : Pattern) : d2386 (change p 224 none) = d159 p := by
  change (if p 162 then d12 (change p 224 none) else d2333 (change p 224 none)) = d159 p
  rw [sub10059, sub10235]
  rfl
theorem sub10295 (p : Pattern) : d2387 (change p 224 none) = d160 p := by
  change (if p 161 then d12 (change p 224 none) else d2386 (change p 224 none)) = d160 p
  rw [sub10059, sub10294]
  rfl
theorem sub10296 (p : Pattern) : d2388 (change p 224 none) = d161 p := by
  change (if p 160 then d12 (change p 224 none) else d2387 (change p 224 none)) = d161 p
  rw [sub10059, sub10295]
  rfl
theorem sub10297 (p : Pattern) : d2389 (change p 224 none) = d162 p := by
  change (if p 141 then d12 (change p 224 none) else d2388 (change p 224 none)) = d162 p
  rw [sub10059, sub10296]
  rfl
theorem sub10298 (p : Pattern) : d2390 (change p 224 none) = d163 p := by
  change (if p 138 then d2389 (change p 224 none) else d2384 (change p 224 none)) = d163 p
  rw [sub10297, sub10292]
  rfl
theorem sub10299 (p : Pattern) : d2391 (change p 224 none) = d164 p := by
  change (if p 116 then d2390 (change p 224 none) else d2385 (change p 224 none)) = d164 p
  rw [sub10298, sub10293]
  rfl
theorem sub10300 (p : Pattern) : d2392 (change p 224 none) = d105 p := by
  change (if p 163 then d2327 (change p 224 none) else d2325 (change p 224 none)) = d105 p
  rw [sub10226, sub10224]
  simp only [ite_self]
theorem sub10301 (p : Pattern) : d2393 (change p 224 none) = d111 p := by
  change (if p 162 then d2331 (change p 224 none) else d2392 (change p 224 none)) = d111 p
  rw [sub10233, sub10300]
  rfl
theorem sub10302 (p : Pattern) : d2394 (change p 224 none) = d114 p := by
  change (if p 161 then d2334 (change p 224 none) else d2393 (change p 224 none)) = d114 p
  rw [sub10236, sub10301]
  rfl
theorem sub10303 (p : Pattern) : d2395 (change p 224 none) = d131 p := by
  change (if p 160 then d2349 (change p 224 none) else d2394 (change p 224 none)) = d131 p
  rw [sub10257, sub10302]
  rfl
theorem sub10304 (p : Pattern) : d2396 (change p 224 none) = d146 p := by
  change (if p 160 then d2367 (change p 224 none) else d2379 (change p 224 none)) = d146 p
  rw [sub10275, sub10287]
  rfl
theorem sub10305 (p : Pattern) : d2397 (change p 224 none) = d147 p := by
  change (if p 141 then d2396 (change p 224 none) else d2395 (change p 224 none)) = d147 p
  rw [sub10304, sub10303]
  rfl
theorem sub10306 (p : Pattern) : d2398 (change p 224 none) = d158 p := by
  change (if p 138 then d2384 (change p 224 none) else d2397 (change p 224 none)) = d158 p
  rw [sub10292, sub10305]
  rfl
theorem sub10307 (p : Pattern) : d2399 (change p 224 none) = d165 p := by
  change (if p 138 then d12 (change p 224 none) else d2384 (change p 224 none)) = d165 p
  rw [sub10059, sub10292]
  rfl
theorem sub10308 (p : Pattern) : d2400 (change p 224 none) = d166 p := by
  change (if p 116 then d2399 (change p 224 none) else d2398 (change p 224 none)) = d166 p
  rw [sub10307, sub10306]
  rfl
theorem sub10309 (p : Pattern) : d2401 (change p 224 none) = d167 p := by
  change (if p 115 then d2400 (change p 224 none) else d2391 (change p 224 none)) = d167 p
  rw [sub10308, sub10299]
  rfl
theorem sub10310 (p : Pattern) : d2402 (change p 224 none) = d168 p := by
  change (if p 71 then d2401 (change p 224 none) else d2296 (change p 224 none)) = d168 p
  rw [sub10309, sub10192]
  rfl
theorem sub10311 (p : Pattern) : d2403 (change p 224 none) = d169 p := by
  change (if p 49 then d2402 (change p 224 none) else d2317 (change p 224 none)) = d169 p
  rw [sub10310, sub10213]
  rfl
theorem sub10312 (p : Pattern) : d2404 (change p 224 none) = d170 p := by
  change (if p 182 then d2213 (change p 224 none) else d2209 (change p 224 none)) = d170 p
  rw [sub10103, sub10096]
  rfl
theorem sub10313 (p : Pattern) : d2405 (change p 224 none) = d171 p := by
  change (if p 163 then d2404 (change p 224 none) else d2232 (change p 224 none)) = d171 p
  rw [sub10312, sub10125]
  rfl
theorem sub10314 (p : Pattern) : d2406 (change p 224 none) = d172 p := by
  change (if p 182 then d2217 (change p 224 none) else d2209 (change p 224 none)) = d172 p
  rw [sub10110, sub10096]
  rfl
theorem sub10315 (p : Pattern) : d2407 (change p 224 none) = d173 p := by
  change (if p 182 then d12 (change p 224 none) else d2212 (change p 224 none)) = d173 p
  rw [sub10059, sub10102]
  rfl
theorem sub10316 (p : Pattern) : d2408 (change p 224 none) = d174 p := by
  change (if p 163 then d2407 (change p 224 none) else d2406 (change p 224 none)) = d174 p
  rw [sub10315, sub10314]
  rfl
theorem sub10317 (p : Pattern) : d2409 (change p 224 none) = d175 p := by
  change (if p 162 then d2408 (change p 224 none) else d2405 (change p 224 none)) = d175 p
  rw [sub10316, sub10313]
  rfl
theorem sub10318 (p : Pattern) : d2410 (change p 224 none) = d176 p := by
  change (if p 163 then d2407 (change p 224 none) else d2244 (change p 224 none)) = d176 p
  rw [sub10315, sub10140]
  rfl
theorem sub10319 (p : Pattern) : d2411 (change p 224 none) = d177 p := by
  change (if p 162 then d2251 (change p 224 none) else d2410 (change p 224 none)) = d177 p
  rw [sub10147, sub10318]
  rfl
end NetHack.Sokoban22Refined85
