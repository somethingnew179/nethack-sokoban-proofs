/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions77
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub9360 (p : Pattern) : d2287 (change p 224 (some 225)) = d16 p := by
  change (if p 163 then d2201 (change p 224 (some 225)) else d2191 (change p 224 (some 225))) = d16 p
  rw [sub9259, sub9246]
  simp only [ite_self]
theorem sub9361 (p : Pattern) : d2288 (change p 224 (some 225)) = d22 p := by
  change (if p 162 then d2202 (change p 224 (some 225)) else d2287 (change p 224 (some 225))) = d22 p
  rw [sub9260, sub9360]
  rfl
theorem sub9362 (p : Pattern) : d2289 (change p 224 (some 225)) = d29 p := by
  change (if p 161 then d2207 (change p 224 (some 225)) else d2288 (change p 224 (some 225))) = d29 p
  rw [sub9268, sub9361]
  rfl
theorem sub9363 (p : Pattern) : d2290 (change p 224 (some 225)) = d52 p := by
  change (if p 160 then d2227 (change p 224 (some 225)) else d2289 (change p 224 (some 225))) = d52 p
  rw [sub9297, sub9362]
  rfl
theorem sub9364 (p : Pattern) : d2291 (change p 224 (some 225)) = d76 p := by
  change (if p 160 then d2253 (change p 224 (some 225)) else d2265 (change p 224 (some 225))) = d76 p
  rw [sub9326, sub9338]
  rfl
theorem sub9365 (p : Pattern) : d2292 (change p 224 (some 225)) = d77 p := by
  change (if p 141 then d2291 (change p 224 (some 225)) else d2290 (change p 224 (some 225))) = d77 p
  rw [sub9364, sub9363]
  rfl
theorem sub9366 (p : Pattern) : d2293 (change p 224 (some 225)) = d88 p := by
  change (if p 138 then d2270 (change p 224 (some 225)) else d2292 (change p 224 (some 225))) = d88 p
  rw [sub9343, sub9365]
  rfl
theorem sub9367 (p : Pattern) : d2294 (change p 224 (some 225)) = d99 p := by
  change (if p 138 then d12 (change p 224 (some 225)) else d2270 (change p 224 (some 225))) = d99 p
  rw [sub9236, sub9343]
  rfl
theorem sub9368 (p : Pattern) : d2295 (change p 224 (some 225)) = d100 p := by
  change (if p 116 then d2294 (change p 224 (some 225)) else d2293 (change p 224 (some 225))) = d100 p
  rw [sub9367, sub9366]
  rfl
theorem sub9369 (p : Pattern) : d2296 (change p 224 (some 225)) = d101 p := by
  change (if p 115 then d2295 (change p 224 (some 225)) else d2286 (change p 224 (some 225))) = d101 p
  rw [sub9368, sub9359]
  rfl
theorem sub9370 (p : Pattern) : d2297 (change p 224 (some 225)) = d14 p := by
  change d14 (change p 224 (some 225)) = d14 p
  exact sub9238 p
theorem sub9371 (p : Pattern) : d2298 (change p 224 (some 225)) = d14 p := by
  change (if p 204 then d2185 (change p 224 (some 225)) else d2297 (change p 224 (some 225))) = d14 p
  rw [sub9240, sub9370]
  simp only [ite_self]
theorem sub9372 (p : Pattern) : d2299 (change p 224 (some 225)) = d16 p := by
  change (if p 182 then d2187 (change p 224 (some 225)) else d2298 (change p 224 (some 225))) = d16 p
  rw [sub9242, sub9371]
  rfl
theorem sub9373 (p : Pattern) : d2300 (change p 224 (some 225)) = d16 p := by
  change (if p 163 then d2195 (change p 224 (some 225)) else d2299 (change p 224 (some 225))) = d16 p
  rw [sub9250, sub9372]
  simp only [ite_self]
theorem sub9374 (p : Pattern) : d2301 (change p 224 (some 225)) = d22 p := by
  change (if p 162 then d2202 (change p 224 (some 225)) else d2300 (change p 224 (some 225))) = d22 p
  rw [sub9260, sub9373]
  rfl
theorem sub9375 (p : Pattern) : d2302 (change p 224 (some 225)) = d29 p := by
  change (if p 161 then d2207 (change p 224 (some 225)) else d2301 (change p 224 (some 225))) = d29 p
  rw [sub9268, sub9374]
  rfl
theorem sub9376 (p : Pattern) : d2303 (change p 224 (some 225)) = d52 p := by
  change (if p 160 then d2227 (change p 224 (some 225)) else d2302 (change p 224 (some 225))) = d52 p
  rw [sub9297, sub9375]
  rfl
theorem sub9377 (p : Pattern) : d2304 (change p 224 (some 225)) = d54 p := by
  change (if p 163 then d2232 (change p 224 (some 225)) else d2191 (change p 224 (some 225))) = d54 p
  rw [sub9302, sub9246]
  rfl
theorem sub9378 (p : Pattern) : d2305 (change p 224 (some 225)) = d56 p := by
  change (if p 162 then d2234 (change p 224 (some 225)) else d2304 (change p 224 (some 225))) = d56 p
  rw [sub9304, sub9377]
  rfl
theorem sub9379 (p : Pattern) : d2306 (change p 224 (some 225)) = d65 p := by
  change (if p 161 then d2242 (change p 224 (some 225)) else d2305 (change p 224 (some 225))) = d65 p
  rw [sub9315, sub9378]
  rfl
theorem sub9380 (p : Pattern) : d2307 (change p 224 (some 225)) = d76 p := by
  change (if p 160 then d2253 (change p 224 (some 225)) else d2306 (change p 224 (some 225))) = d76 p
  rw [sub9326, sub9379]
  rfl
theorem sub9381 (p : Pattern) : d2308 (change p 224 (some 225)) = d77 p := by
  change (if p 141 then d2307 (change p 224 (some 225)) else d2303 (change p 224 (some 225))) = d77 p
  rw [sub9380, sub9376]
  rfl
theorem sub9382 (p : Pattern) : d2309 (change p 224 (some 225)) = d88 p := by
  change (if p 138 then d2270 (change p 224 (some 225)) else d2308 (change p 224 (some 225))) = d88 p
  rw [sub9343, sub9381]
  rfl
theorem sub9383 (p : Pattern) : d2310 (change p 224 (some 225)) = d97 p := by
  change (if p 138 then d2284 (change p 224 (some 225)) else d2270 (change p 224 (some 225))) = d97 p
  rw [sub9357, sub9343]
  rfl
theorem sub9384 (p : Pattern) : d2311 (change p 224 (some 225)) = d98 p := by
  change (if p 116 then d2310 (change p 224 (some 225)) else d2309 (change p 224 (some 225))) = d98 p
  rw [sub9383, sub9382]
  rfl
theorem sub9385 (p : Pattern) : d2312 (change p 224 (some 225)) = d52 p := by
  change (if p 160 then d2227 (change p 224 (some 225)) else d2274 (change p 224 (some 225))) = d52 p
  rw [sub9297, sub9347]
  rfl
theorem sub9386 (p : Pattern) : d2313 (change p 224 (some 225)) = d77 p := by
  change (if p 141 then d2291 (change p 224 (some 225)) else d2312 (change p 224 (some 225))) = d77 p
  rw [sub9364, sub9385]
  rfl
theorem sub9387 (p : Pattern) : d2314 (change p 224 (some 225)) = d88 p := by
  change (if p 138 then d2270 (change p 224 (some 225)) else d2313 (change p 224 (some 225))) = d88 p
  rw [sub9343, sub9386]
  rfl
theorem sub9388 (p : Pattern) : d2315 (change p 224 (some 225)) = d100 p := by
  change (if p 116 then d2294 (change p 224 (some 225)) else d2314 (change p 224 (some 225))) = d100 p
  rw [sub9367, sub9387]
  rfl
theorem sub9389 (p : Pattern) : d2316 (change p 224 (some 225)) = d101 p := by
  change (if p 115 then d2315 (change p 224 (some 225)) else d2311 (change p 224 (some 225))) = d101 p
  rw [sub9388, sub9384]
  rfl
theorem sub9390 (p : Pattern) : d2317 (change p 224 (some 225)) = d101 p := by
  change (if p 71 then d2316 (change p 224 (some 225)) else d2296 (change p 224 (some 225))) = d101 p
  rw [sub9389, sub9369]
  simp only [ite_self]
theorem sub9391 (p : Pattern) : d1 (change p 224 (some 225)) = d1 p := by
  rfl
theorem sub9392 (p : Pattern) : d102 (change p 224 (some 225)) = d102 p := by
  change (if p 247 then d12 (change p 224 (some 225)) else d1 (change p 224 (some 225))) = d102 p
  rw [sub9236, sub9391]
  rfl
theorem sub9393 (p : Pattern) : d103 (change p 224 (some 225)) = d103 p := by
  change (if p 246 then d102 (change p 224 (some 225)) else d1 (change p 224 (some 225))) = d103 p
  rw [sub9392, sub9391]
  rfl
theorem sub9394 (p : Pattern) : d2318 (change p 224 (some 225)) = d103 p := by
  change d103 (change p 224 (some 225)) = d103 p
  exact sub9393 p
theorem sub9395 (p : Pattern) : d2319 (change p 224 (some 225)) = d103 p := by
  change d103 (change p 224 (some 225)) = d103 p
  exact sub9393 p
theorem sub9396 (p : Pattern) : d2320 (change p 224 (some 225)) = d103 p := by
  change (if p 204 then d2319 (change p 224 (some 225)) else d2318 (change p 224 (some 225))) = d103 p
  rw [sub9395, sub9394]
  simp only [ite_self]
theorem sub9397 (p : Pattern) : d2321 (change p 224 (some 225)) = d104 p := by
  change (if p 204 then d12 (change p 224 (some 225)) else d2319 (change p 224 (some 225))) = d104 p
  rw [sub9236, sub9395]
  rfl
theorem sub9398 (p : Pattern) : d2322 (change p 224 (some 225)) = d105 p := by
  change (if p 182 then d2321 (change p 224 (some 225)) else d2320 (change p 224 (some 225))) = d105 p
  rw [sub9397, sub9396]
  rfl
theorem sub9399 (p : Pattern) : d2323 (change p 224 (some 225)) = d103 p := by
  change d103 (change p 224 (some 225)) = d103 p
  exact sub9393 p
theorem sub9400 (p : Pattern) : d2324 (change p 224 (some 225)) = d103 p := by
  change (if p 204 then d2319 (change p 224 (some 225)) else d2323 (change p 224 (some 225))) = d103 p
  rw [sub9395, sub9399]
  simp only [ite_self]
theorem sub9401 (p : Pattern) : d2325 (change p 224 (some 225)) = d105 p := by
  change (if p 182 then d2321 (change p 224 (some 225)) else d2324 (change p 224 (some 225))) = d105 p
  rw [sub9397, sub9400]
  rfl
theorem sub9402 (p : Pattern) : d2326 (change p 224 (some 225)) = d105 p := by
  change (if p 163 then d2325 (change p 224 (some 225)) else d2322 (change p 224 (some 225))) = d105 p
  rw [sub9401, sub9398]
  simp only [ite_self]
theorem sub9403 (p : Pattern) : d2327 (change p 224 (some 225)) = d105 p := by
  change (if p 182 then d2321 (change p 224 (some 225)) else d2319 (change p 224 (some 225))) = d105 p
  rw [sub9397, sub9395]
  rfl
theorem sub9404 (p : Pattern) : d5 (change p 224 (some 225)) = d5 p := by
  rfl
theorem sub9405 (p : Pattern) : d106 (change p 224 (some 225)) = d106 p := by
  change (if p 247 then d12 (change p 224 (some 225)) else d5 (change p 224 (some 225))) = d106 p
  rw [sub9236, sub9404]
  rfl
theorem sub9406 (p : Pattern) : d107 (change p 224 (some 225)) = d107 p := by
  change (if p 246 then d106 (change p 224 (some 225)) else d5 (change p 224 (some 225))) = d107 p
  rw [sub9405, sub9404]
  rfl
theorem sub9407 (p : Pattern) : d2328 (change p 224 (some 225)) = d107 p := by
  change d107 (change p 224 (some 225)) = d107 p
  exact sub9406 p
theorem sub9408 (p : Pattern) : d2329 (change p 224 (some 225)) = d108 p := by
  change (if p 204 then d12 (change p 224 (some 225)) else d2328 (change p 224 (some 225))) = d108 p
  rw [sub9236, sub9407]
  rfl
theorem sub9409 (p : Pattern) : d2330 (change p 224 (some 225)) = d109 p := by
  change (if p 182 then d2329 (change p 224 (some 225)) else d2328 (change p 224 (some 225))) = d109 p
  rw [sub9408, sub9407]
  rfl
theorem sub9410 (p : Pattern) : d2331 (change p 224 (some 225)) = d110 p := by
  change (if p 163 then d2330 (change p 224 (some 225)) else d2327 (change p 224 (some 225))) = d110 p
  rw [sub9409, sub9403]
  rfl
theorem sub9411 (p : Pattern) : d2332 (change p 224 (some 225)) = d111 p := by
  change (if p 162 then d2331 (change p 224 (some 225)) else d2326 (change p 224 (some 225))) = d111 p
  rw [sub9410, sub9402]
  rfl
theorem sub9412 (p : Pattern) : d2333 (change p 224 (some 225)) = d112 p := by
  change (if p 163 then d12 (change p 224 (some 225)) else d2238 (change p 224 (some 225))) = d112 p
  rw [sub9236, sub9311]
  rfl
theorem sub9413 (p : Pattern) : d2334 (change p 224 (some 225)) = d113 p := by
  change (if p 162 then d2333 (change p 224 (some 225)) else d2331 (change p 224 (some 225))) = d113 p
  rw [sub9412, sub9410]
  rfl
theorem sub9414 (p : Pattern) : d2335 (change p 224 (some 225)) = d114 p := by
  change (if p 161 then d2334 (change p 224 (some 225)) else d2332 (change p 224 (some 225))) = d114 p
  rw [sub9413, sub9411]
  rfl
theorem sub9415 (p : Pattern) : d3 (change p 224 (some 225)) = d3 p := by
  rfl
theorem sub9416 (p : Pattern) : d115 (change p 224 (some 225)) = d115 p := by
  change (if p 247 then d12 (change p 224 (some 225)) else d3 (change p 224 (some 225))) = d115 p
  rw [sub9236, sub9415]
  rfl
theorem sub9417 (p : Pattern) : d116 (change p 224 (some 225)) = d116 p := by
  change (if p 246 then d115 (change p 224 (some 225)) else d3 (change p 224 (some 225))) = d116 p
  rw [sub9416, sub9415]
  rfl
theorem sub9418 (p : Pattern) : d2336 (change p 224 (some 225)) = d116 p := by
  change d116 (change p 224 (some 225)) = d116 p
  exact sub9417 p
theorem sub9419 (p : Pattern) : d2337 (change p 224 (some 225)) = d117 p := by
  change (if p 204 then d12 (change p 224 (some 225)) else d2336 (change p 224 (some 225))) = d117 p
  rw [sub9236, sub9418]
  rfl
theorem sub9420 (p : Pattern) : d2338 (change p 224 (some 225)) = d118 p := by
  change (if p 182 then d2337 (change p 224 (some 225)) else d2319 (change p 224 (some 225))) = d118 p
  rw [sub9419, sub9395]
  rfl
theorem sub9421 (p : Pattern) : d7 (change p 224 (some 225)) = d7 p := by
  rfl
theorem sub9422 (p : Pattern) : d119 (change p 224 (some 225)) = d119 p := by
  change (if p 247 then d12 (change p 224 (some 225)) else d7 (change p 224 (some 225))) = d119 p
  rw [sub9236, sub9421]
  rfl
theorem sub9423 (p : Pattern) : d120 (change p 224 (some 225)) = d120 p := by
  change (if p 246 then d119 (change p 224 (some 225)) else d7 (change p 224 (some 225))) = d120 p
  rw [sub9422, sub9421]
  rfl
theorem sub9424 (p : Pattern) : d2339 (change p 224 (some 225)) = d120 p := by
  change d120 (change p 224 (some 225)) = d120 p
  exact sub9423 p
theorem sub9425 (p : Pattern) : d2340 (change p 224 (some 225)) = d121 p := by
  change (if p 204 then d12 (change p 224 (some 225)) else d2339 (change p 224 (some 225))) = d121 p
  rw [sub9236, sub9424]
  rfl
theorem sub9426 (p : Pattern) : d2341 (change p 224 (some 225)) = d122 p := by
  change (if p 182 then d2340 (change p 224 (some 225)) else d2319 (change p 224 (some 225))) = d122 p
  rw [sub9425, sub9395]
  rfl
theorem sub9427 (p : Pattern) : d2342 (change p 224 (some 225)) = d123 p := by
  change (if p 163 then d2341 (change p 224 (some 225)) else d2338 (change p 224 (some 225))) = d123 p
  rw [sub9426, sub9420]
  rfl
theorem sub9428 (p : Pattern) : d2343 (change p 224 (some 225)) = d124 p := by
  change (if p 182 then d12 (change p 224 (some 225)) else d2319 (change p 224 (some 225))) = d124 p
  rw [sub9236, sub9395]
  rfl
theorem sub9429 (p : Pattern) : d2344 (change p 224 (some 225)) = d125 p := by
  change (if p 182 then d12 (change p 224 (some 225)) else d2328 (change p 224 (some 225))) = d125 p
  rw [sub9236, sub9407]
  rfl
theorem sub9430 (p : Pattern) : d2345 (change p 224 (some 225)) = d126 p := by
  change (if p 163 then d2344 (change p 224 (some 225)) else d2343 (change p 224 (some 225))) = d126 p
  rw [sub9429, sub9428]
  rfl
theorem sub9431 (p : Pattern) : d2346 (change p 224 (some 225)) = d127 p := by
  change (if p 162 then d2345 (change p 224 (some 225)) else d2342 (change p 224 (some 225))) = d127 p
  rw [sub9430, sub9427]
  rfl
theorem sub9432 (p : Pattern) : d2347 (change p 224 (some 225)) = d128 p := by
  change (if p 163 then d12 (change p 224 (some 225)) else d2248 (change p 224 (some 225))) = d128 p
  rw [sub9236, sub9321]
  rfl
theorem sub9433 (p : Pattern) : d2348 (change p 224 (some 225)) = d129 p := by
  change (if p 162 then d2347 (change p 224 (some 225)) else d2345 (change p 224 (some 225))) = d129 p
  rw [sub9432, sub9430]
  rfl
theorem sub9434 (p : Pattern) : d2349 (change p 224 (some 225)) = d130 p := by
  change (if p 161 then d2348 (change p 224 (some 225)) else d2346 (change p 224 (some 225))) = d130 p
  rw [sub9433, sub9431]
  rfl
theorem sub9435 (p : Pattern) : d2350 (change p 224 (some 225)) = d131 p := by
  change (if p 160 then d2349 (change p 224 (some 225)) else d2335 (change p 224 (some 225))) = d131 p
  rw [sub9434, sub9414]
  rfl
theorem sub9436 (p : Pattern) : d2351 (change p 224 (some 225)) = d103 p := by
  change d103 (change p 224 (some 225)) = d103 p
  exact sub9393 p
theorem sub9437 (p : Pattern) : d2352 (change p 224 (some 225)) = d103 p := by
  change (if p 204 then d2319 (change p 224 (some 225)) else d2351 (change p 224 (some 225))) = d103 p
  rw [sub9395, sub9436]
  simp only [ite_self]
theorem sub9438 (p : Pattern) : d2353 (change p 224 (some 225)) = d105 p := by
  change (if p 182 then d2321 (change p 224 (some 225)) else d2352 (change p 224 (some 225))) = d105 p
  rw [sub9397, sub9437]
  rfl
theorem sub9439 (p : Pattern) : d2354 (change p 224 (some 225)) = d132 p := by
  change (if p 182 then d2337 (change p 224 (some 225)) else d2336 (change p 224 (some 225))) = d132 p
  rw [sub9419, sub9418]
  rfl
theorem sub9440 (p : Pattern) : d2355 (change p 224 (some 225)) = d133 p := by
  change (if p 163 then d2354 (change p 224 (some 225)) else d2353 (change p 224 (some 225))) = d133 p
  rw [sub9439, sub9438]
  rfl
theorem sub9441 (p : Pattern) : d2356 (change p 224 (some 225)) = d134 p := by
  change (if p 163 then d2238 (change p 224 (some 225)) else d2330 (change p 224 (some 225))) = d134 p
  rw [sub9311, sub9409]
  rfl
theorem sub9442 (p : Pattern) : d2357 (change p 224 (some 225)) = d135 p := by
  change (if p 162 then d2356 (change p 224 (some 225)) else d2355 (change p 224 (some 225))) = d135 p
  rw [sub9441, sub9440]
  rfl
theorem sub9443 (p : Pattern) : d2358 (change p 224 (some 225)) = d136 p := by
  change (if p 163 then d2240 (change p 224 (some 225)) else d2330 (change p 224 (some 225))) = d136 p
  rw [sub9313, sub9409]
  rfl
theorem sub9444 (p : Pattern) : d2359 (change p 224 (some 225)) = d137 p := by
  change (if p 162 then d12 (change p 224 (some 225)) else d2358 (change p 224 (some 225))) = d137 p
  rw [sub9236, sub9443]
  rfl
theorem sub9445 (p : Pattern) : d2360 (change p 224 (some 225)) = d138 p := by
  change (if p 161 then d2359 (change p 224 (some 225)) else d2357 (change p 224 (some 225))) = d138 p
  rw [sub9444, sub9442]
  rfl
theorem sub9446 (p : Pattern) : d2361 (change p 224 (some 225)) = d139 p := by
  change (if p 182 then d12 (change p 224 (some 225)) else d2336 (change p 224 (some 225))) = d139 p
  rw [sub9236, sub9418]
  rfl
theorem sub9447 (p : Pattern) : d2362 (change p 224 (some 225)) = d140 p := by
  change (if p 163 then d2361 (change p 224 (some 225)) else d2341 (change p 224 (some 225))) = d140 p
  rw [sub9446, sub9426]
  rfl
theorem sub9448 (p : Pattern) : d2363 (change p 224 (some 225)) = d141 p := by
  change (if p 163 then d2248 (change p 224 (some 225)) else d2344 (change p 224 (some 225))) = d141 p
  rw [sub9321, sub9429]
  rfl
theorem sub9449 (p : Pattern) : d2364 (change p 224 (some 225)) = d142 p := by
  change (if p 162 then d2363 (change p 224 (some 225)) else d2362 (change p 224 (some 225))) = d142 p
  rw [sub9448, sub9447]
  rfl
theorem sub9450 (p : Pattern) : d2365 (change p 224 (some 225)) = d143 p := by
  change (if p 163 then d2250 (change p 224 (some 225)) else d2344 (change p 224 (some 225))) = d143 p
  rw [sub9323, sub9429]
  rfl
theorem sub9451 (p : Pattern) : d2366 (change p 224 (some 225)) = d144 p := by
  change (if p 162 then d12 (change p 224 (some 225)) else d2365 (change p 224 (some 225))) = d144 p
  rw [sub9236, sub9450]
  rfl
theorem sub9452 (p : Pattern) : d2367 (change p 224 (some 225)) = d145 p := by
  change (if p 161 then d2366 (change p 224 (some 225)) else d2364 (change p 224 (some 225))) = d145 p
  rw [sub9451, sub9449]
  rfl
theorem sub9453 (p : Pattern) : d2368 (change p 224 (some 225)) = d146 p := by
  change (if p 160 then d2367 (change p 224 (some 225)) else d2360 (change p 224 (some 225))) = d146 p
  rw [sub9452, sub9445]
  rfl
theorem sub9454 (p : Pattern) : d2369 (change p 224 (some 225)) = d147 p := by
  change (if p 141 then d2368 (change p 224 (some 225)) else d2350 (change p 224 (some 225))) = d147 p
  rw [sub9453, sub9435]
  rfl
theorem sub9455 (p : Pattern) : d2370 (change p 224 (some 225)) = d111 p := by
  change (if p 162 then d2331 (change p 224 (some 225)) else d2327 (change p 224 (some 225))) = d111 p
  rw [sub9410, sub9403]
  rfl
theorem sub9456 (p : Pattern) : d2371 (change p 224 (some 225)) = d114 p := by
  change (if p 161 then d2334 (change p 224 (some 225)) else d2370 (change p 224 (some 225))) = d114 p
  rw [sub9413, sub9455]
  rfl
theorem sub9457 (p : Pattern) : d2372 (change p 224 (some 225)) = d148 p := by
  change (if p 182 then d2340 (change p 224 (some 225)) else d2339 (change p 224 (some 225))) = d148 p
  rw [sub9425, sub9424]
  rfl
theorem sub9458 (p : Pattern) : d2373 (change p 224 (some 225)) = d149 p := by
  change (if p 163 then d2372 (change p 224 (some 225)) else d2354 (change p 224 (some 225))) = d149 p
  rw [sub9457, sub9439]
  rfl
theorem sub9459 (p : Pattern) : d2374 (change p 224 (some 225)) = d150 p := by
  change (if p 162 then d12 (change p 224 (some 225)) else d2373 (change p 224 (some 225))) = d150 p
  rw [sub9236, sub9458]
  rfl
theorem sub9460 (p : Pattern) : d2375 (change p 224 (some 225)) = d151 p := by
  change (if p 161 then d12 (change p 224 (some 225)) else d2374 (change p 224 (some 225))) = d151 p
  rw [sub9236, sub9459]
  rfl
theorem sub9461 (p : Pattern) : d2376 (change p 224 (some 225)) = d152 p := by
  change (if p 160 then d2375 (change p 224 (some 225)) else d2371 (change p 224 (some 225))) = d152 p
  rw [sub9460, sub9456]
  rfl
theorem sub9462 (p : Pattern) : d2377 (change p 224 (some 225)) = d133 p := by
  change (if p 163 then d2354 (change p 224 (some 225)) else d2327 (change p 224 (some 225))) = d133 p
  rw [sub9439, sub9403]
  rfl
theorem sub9463 (p : Pattern) : d2378 (change p 224 (some 225)) = d135 p := by
  change (if p 162 then d2356 (change p 224 (some 225)) else d2377 (change p 224 (some 225))) = d135 p
  rw [sub9441, sub9462]
  rfl
theorem sub9464 (p : Pattern) : d2379 (change p 224 (some 225)) = d138 p := by
  change (if p 161 then d2359 (change p 224 (some 225)) else d2378 (change p 224 (some 225))) = d138 p
  rw [sub9444, sub9463]
  rfl
theorem sub9465 (p : Pattern) : d2380 (change p 224 (some 225)) = d153 p := by
  change (if p 163 then d12 (change p 224 (some 225)) else d2372 (change p 224 (some 225))) = d153 p
  rw [sub9236, sub9457]
  rfl
theorem sub9466 (p : Pattern) : d2381 (change p 224 (some 225)) = d154 p := by
  change (if p 162 then d12 (change p 224 (some 225)) else d2380 (change p 224 (some 225))) = d154 p
  rw [sub9236, sub9465]
  rfl
theorem sub9467 (p : Pattern) : d2382 (change p 224 (some 225)) = d155 p := by
  change (if p 161 then d12 (change p 224 (some 225)) else d2381 (change p 224 (some 225))) = d155 p
  rw [sub9236, sub9466]
  rfl
theorem sub9468 (p : Pattern) : d2383 (change p 224 (some 225)) = d156 p := by
  change (if p 160 then d2382 (change p 224 (some 225)) else d2379 (change p 224 (some 225))) = d156 p
  rw [sub9467, sub9464]
  rfl
theorem sub9469 (p : Pattern) : d2384 (change p 224 (some 225)) = d157 p := by
  change (if p 141 then d2383 (change p 224 (some 225)) else d2376 (change p 224 (some 225))) = d157 p
  rw [sub9468, sub9461]
  rfl
theorem sub9470 (p : Pattern) : d2385 (change p 224 (some 225)) = d158 p := by
  change (if p 138 then d2384 (change p 224 (some 225)) else d2369 (change p 224 (some 225))) = d158 p
  rw [sub9469, sub9454]
  rfl
theorem sub9471 (p : Pattern) : d2386 (change p 224 (some 225)) = d159 p := by
  change (if p 162 then d12 (change p 224 (some 225)) else d2333 (change p 224 (some 225))) = d159 p
  rw [sub9236, sub9412]
  rfl
theorem sub9472 (p : Pattern) : d2387 (change p 224 (some 225)) = d160 p := by
  change (if p 161 then d12 (change p 224 (some 225)) else d2386 (change p 224 (some 225))) = d160 p
  rw [sub9236, sub9471]
  rfl
theorem sub9473 (p : Pattern) : d2388 (change p 224 (some 225)) = d161 p := by
  change (if p 160 then d12 (change p 224 (some 225)) else d2387 (change p 224 (some 225))) = d161 p
  rw [sub9236, sub9472]
  rfl
theorem sub9474 (p : Pattern) : d2389 (change p 224 (some 225)) = d162 p := by
  change (if p 141 then d12 (change p 224 (some 225)) else d2388 (change p 224 (some 225))) = d162 p
  rw [sub9236, sub9473]
  rfl
theorem sub9475 (p : Pattern) : d2390 (change p 224 (some 225)) = d163 p := by
  change (if p 138 then d2389 (change p 224 (some 225)) else d2384 (change p 224 (some 225))) = d163 p
  rw [sub9474, sub9469]
  rfl
theorem sub9476 (p : Pattern) : d2391 (change p 224 (some 225)) = d164 p := by
  change (if p 116 then d2390 (change p 224 (some 225)) else d2385 (change p 224 (some 225))) = d164 p
  rw [sub9475, sub9470]
  rfl
theorem sub9477 (p : Pattern) : d2392 (change p 224 (some 225)) = d105 p := by
  change (if p 163 then d2327 (change p 224 (some 225)) else d2325 (change p 224 (some 225))) = d105 p
  rw [sub9403, sub9401]
  simp only [ite_self]
theorem sub9478 (p : Pattern) : d2393 (change p 224 (some 225)) = d111 p := by
  change (if p 162 then d2331 (change p 224 (some 225)) else d2392 (change p 224 (some 225))) = d111 p
  rw [sub9410, sub9477]
  rfl
theorem sub9479 (p : Pattern) : d2394 (change p 224 (some 225)) = d114 p := by
  change (if p 161 then d2334 (change p 224 (some 225)) else d2393 (change p 224 (some 225))) = d114 p
  rw [sub9413, sub9478]
  rfl
end NetHack.Sokoban22Refined85
