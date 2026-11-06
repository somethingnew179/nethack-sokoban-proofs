/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions68
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub8280 (p : Pattern) : d2258 (change p 224 (some 246)) = d5321 p := by
  change (if p 182 then d2213 (change p 224 (some 246)) else d2212 (change p 224 (some 246))) = d5321 p
  rw [sub8229, sub8228]
  rfl
theorem sub8281 (p : Pattern) : d2259 (change p 224 (some 246)) = d5322 p := by
  change (if p 163 then d2258 (change p 224 (some 246)) else d2232 (change p 224 (some 246))) = d5322 p
  rw [sub8280, sub8251]
  rfl
theorem sub8282 (p : Pattern) : d2260 (change p 224 (some 246)) = d5323 p := by
  change (if p 162 then d2241 (change p 224 (some 246)) else d2259 (change p 224 (some 246))) = d5323 p
  rw [sub8263, sub8281]
  rfl
theorem sub8283 (p : Pattern) : d2261 (change p 224 (some 246)) = d5324 p := by
  change (if p 161 then d12 (change p 224 (some 246)) else d2260 (change p 224 (some 246))) = d5324 p
  rw [sub8185, sub8282]
  rfl
theorem sub8284 (p : Pattern) : d2262 (change p 224 (some 246)) = d5325 p := by
  change (if p 160 then d2261 (change p 224 (some 246)) else d2257 (change p 224 (some 246))) = d5325 p
  rw [sub8283, sub8279]
  rfl
theorem sub8285 (p : Pattern) : d2263 (change p 224 (some 246)) = d5299 p := by
  change (if p 163 then d2232 (change p 224 (some 246)) else d2201 (change p 224 (some 246))) = d5299 p
  rw [sub8251, sub8208]
  rfl
theorem sub8286 (p : Pattern) : d2264 (change p 224 (some 246)) = d5301 p := by
  change (if p 162 then d2234 (change p 224 (some 246)) else d2263 (change p 224 (some 246))) = d5301 p
  rw [sub8253, sub8285]
  rfl
theorem sub8287 (p : Pattern) : d2265 (change p 224 (some 246)) = d5308 p := by
  change (if p 161 then d2242 (change p 224 (some 246)) else d2264 (change p 224 (some 246))) = d5308 p
  rw [sub8264, sub8286]
  rfl
theorem sub8288 (p : Pattern) : d2266 (change p 224 (some 246)) = d5326 p := by
  change (if p 163 then d12 (change p 224 (some 246)) else d2258 (change p 224 (some 246))) = d5326 p
  rw [sub8185, sub8280]
  rfl
theorem sub8289 (p : Pattern) : d2267 (change p 224 (some 246)) = d5327 p := by
  change (if p 162 then d12 (change p 224 (some 246)) else d2266 (change p 224 (some 246))) = d5327 p
  rw [sub8185, sub8288]
  rfl
theorem sub8290 (p : Pattern) : d2268 (change p 224 (some 246)) = d5328 p := by
  change (if p 161 then d12 (change p 224 (some 246)) else d2267 (change p 224 (some 246))) = d5328 p
  rw [sub8185, sub8289]
  rfl
theorem sub8291 (p : Pattern) : d2269 (change p 224 (some 246)) = d5329 p := by
  change (if p 160 then d2268 (change p 224 (some 246)) else d2265 (change p 224 (some 246))) = d5329 p
  rw [sub8290, sub8287]
  rfl
theorem sub8292 (p : Pattern) : d2270 (change p 224 (some 246)) = d5330 p := by
  change (if p 141 then d2269 (change p 224 (some 246)) else d2262 (change p 224 (some 246))) = d5330 p
  rw [sub8291, sub8284]
  rfl
theorem sub8293 (p : Pattern) : d2271 (change p 224 (some 246)) = d5331 p := by
  change (if p 138 then d2270 (change p 224 (some 246)) else d2255 (change p 224 (some 246))) = d5331 p
  rw [sub8292, sub8277]
  rfl
theorem sub8294 (p : Pattern) : d2272 (change p 224 (some 246)) = d5271 p := by
  change (if p 163 then d2201 (change p 224 (some 246)) else d2195 (change p 224 (some 246))) = d5271 p
  rw [sub8208, sub8199]
  simp only [ite_self]
theorem sub8295 (p : Pattern) : d2273 (change p 224 (some 246)) = d5275 p := by
  change (if p 162 then d2202 (change p 224 (some 246)) else d2272 (change p 224 (some 246))) = d5275 p
  rw [sub8209, sub8294]
  rfl
theorem sub8296 (p : Pattern) : d2274 (change p 224 (some 246)) = d5280 p := by
  change (if p 161 then d2207 (change p 224 (some 246)) else d2273 (change p 224 (some 246))) = d5280 p
  rw [sub8217, sub8295]
  rfl
theorem sub8297 (p : Pattern) : d2275 (change p 224 (some 246)) = d5325 p := by
  change (if p 160 then d2261 (change p 224 (some 246)) else d2274 (change p 224 (some 246))) = d5325 p
  rw [sub8283, sub8296]
  rfl
theorem sub8298 (p : Pattern) : d2276 (change p 224 (some 246)) = d5330 p := by
  change (if p 141 then d2269 (change p 224 (some 246)) else d2275 (change p 224 (some 246))) = d5330 p
  rw [sub8291, sub8297]
  rfl
theorem sub8299 (p : Pattern) : d2277 (change p 224 (some 246)) = d5332 p := by
  change (if p 163 then d2240 (change p 224 (some 246)) else d2205 (change p 224 (some 246))) = d5332 p
  rw [sub8262, sub8215]
  rfl
theorem sub8300 (p : Pattern) : d2278 (change p 224 (some 246)) = d5333 p := by
  change (if p 162 then d2241 (change p 224 (some 246)) else d2277 (change p 224 (some 246))) = d5333 p
  rw [sub8263, sub8299]
  rfl
theorem sub8301 (p : Pattern) : d2279 (change p 224 (some 246)) = d5334 p := by
  change (if p 162 then d12 (change p 224 (some 246)) else d2241 (change p 224 (some 246))) = d5334 p
  rw [sub8185, sub8263]
  rfl
theorem sub8302 (p : Pattern) : d2280 (change p 224 (some 246)) = d5335 p := by
  change (if p 161 then d2279 (change p 224 (some 246)) else d2278 (change p 224 (some 246))) = d5335 p
  rw [sub8301, sub8300]
  rfl
theorem sub8303 (p : Pattern) : d2281 (change p 224 (some 246)) = d5336 p := by
  change (if p 161 then d12 (change p 224 (some 246)) else d2279 (change p 224 (some 246))) = d5336 p
  rw [sub8185, sub8301]
  rfl
theorem sub8304 (p : Pattern) : d2282 (change p 224 (some 246)) = d5337 p := by
  change (if p 160 then d2281 (change p 224 (some 246)) else d2280 (change p 224 (some 246))) = d5337 p
  rw [sub8303, sub8302]
  rfl
theorem sub8305 (p : Pattern) : d2283 (change p 224 (some 246)) = d5338 p := by
  change (if p 160 then d12 (change p 224 (some 246)) else d2281 (change p 224 (some 246))) = d5338 p
  rw [sub8185, sub8303]
  rfl
theorem sub8306 (p : Pattern) : d2284 (change p 224 (some 246)) = d5339 p := by
  change (if p 141 then d2283 (change p 224 (some 246)) else d2282 (change p 224 (some 246))) = d5339 p
  rw [sub8305, sub8304]
  rfl
theorem sub8307 (p : Pattern) : d2285 (change p 224 (some 246)) = d5340 p := by
  change (if p 138 then d2284 (change p 224 (some 246)) else d2276 (change p 224 (some 246))) = d5340 p
  rw [sub8306, sub8298]
  rfl
theorem sub8308 (p : Pattern) : d2286 (change p 224 (some 246)) = d5341 p := by
  change (if p 116 then d2285 (change p 224 (some 246)) else d2271 (change p 224 (some 246))) = d5341 p
  rw [sub8307, sub8293]
  rfl
theorem sub8309 (p : Pattern) : d2287 (change p 224 (some 246)) = d5271 p := by
  change (if p 163 then d2201 (change p 224 (some 246)) else d2191 (change p 224 (some 246))) = d5271 p
  rw [sub8208, sub8195]
  simp only [ite_self]
theorem sub8310 (p : Pattern) : d2288 (change p 224 (some 246)) = d5275 p := by
  change (if p 162 then d2202 (change p 224 (some 246)) else d2287 (change p 224 (some 246))) = d5275 p
  rw [sub8209, sub8309]
  rfl
theorem sub8311 (p : Pattern) : d2289 (change p 224 (some 246)) = d5280 p := by
  change (if p 161 then d2207 (change p 224 (some 246)) else d2288 (change p 224 (some 246))) = d5280 p
  rw [sub8217, sub8310]
  rfl
theorem sub8312 (p : Pattern) : d2290 (change p 224 (some 246)) = d5297 p := by
  change (if p 160 then d2227 (change p 224 (some 246)) else d2289 (change p 224 (some 246))) = d5297 p
  rw [sub8246, sub8311]
  rfl
theorem sub8313 (p : Pattern) : d2291 (change p 224 (some 246)) = d5319 p := by
  change (if p 160 then d2253 (change p 224 (some 246)) else d2265 (change p 224 (some 246))) = d5319 p
  rw [sub8275, sub8287]
  rfl
theorem sub8314 (p : Pattern) : d2292 (change p 224 (some 246)) = d5320 p := by
  change (if p 141 then d2291 (change p 224 (some 246)) else d2290 (change p 224 (some 246))) = d5320 p
  rw [sub8313, sub8312]
  rfl
theorem sub8315 (p : Pattern) : d2293 (change p 224 (some 246)) = d5331 p := by
  change (if p 138 then d2270 (change p 224 (some 246)) else d2292 (change p 224 (some 246))) = d5331 p
  rw [sub8292, sub8314]
  rfl
theorem sub8316 (p : Pattern) : d2294 (change p 224 (some 246)) = d5342 p := by
  change (if p 138 then d12 (change p 224 (some 246)) else d2270 (change p 224 (some 246))) = d5342 p
  rw [sub8185, sub8292]
  rfl
theorem sub8317 (p : Pattern) : d2295 (change p 224 (some 246)) = d5343 p := by
  change (if p 116 then d2294 (change p 224 (some 246)) else d2293 (change p 224 (some 246))) = d5343 p
  rw [sub8316, sub8315]
  rfl
theorem sub8318 (p : Pattern) : d2296 (change p 224 (some 246)) = d5344 p := by
  change (if p 115 then d2295 (change p 224 (some 246)) else d2286 (change p 224 (some 246))) = d5344 p
  rw [sub8317, sub8308]
  rfl
theorem sub8319 (p : Pattern) : d2297 (change p 224 (some 246)) = d13 p := by
  change d14 (change p 224 (some 246)) = d13 p
  exact sub8187 p
theorem sub8320 (p : Pattern) : d2298 (change p 224 (some 246)) = d13 p := by
  change (if p 204 then d2185 (change p 224 (some 246)) else d2297 (change p 224 (some 246))) = d13 p
  rw [sub8189, sub8319]
  simp only [ite_self]
theorem sub8321 (p : Pattern) : d2299 (change p 224 (some 246)) = d5271 p := by
  change (if p 182 then d2187 (change p 224 (some 246)) else d2298 (change p 224 (some 246))) = d5271 p
  rw [sub8191, sub8320]
  rfl
theorem sub8322 (p : Pattern) : d2300 (change p 224 (some 246)) = d5271 p := by
  change (if p 163 then d2195 (change p 224 (some 246)) else d2299 (change p 224 (some 246))) = d5271 p
  rw [sub8199, sub8321]
  simp only [ite_self]
theorem sub8323 (p : Pattern) : d2301 (change p 224 (some 246)) = d5275 p := by
  change (if p 162 then d2202 (change p 224 (some 246)) else d2300 (change p 224 (some 246))) = d5275 p
  rw [sub8209, sub8322]
  rfl
theorem sub8324 (p : Pattern) : d2302 (change p 224 (some 246)) = d5280 p := by
  change (if p 161 then d2207 (change p 224 (some 246)) else d2301 (change p 224 (some 246))) = d5280 p
  rw [sub8217, sub8323]
  rfl
theorem sub8325 (p : Pattern) : d2303 (change p 224 (some 246)) = d5297 p := by
  change (if p 160 then d2227 (change p 224 (some 246)) else d2302 (change p 224 (some 246))) = d5297 p
  rw [sub8246, sub8324]
  rfl
theorem sub8326 (p : Pattern) : d2304 (change p 224 (some 246)) = d5299 p := by
  change (if p 163 then d2232 (change p 224 (some 246)) else d2191 (change p 224 (some 246))) = d5299 p
  rw [sub8251, sub8195]
  rfl
theorem sub8327 (p : Pattern) : d2305 (change p 224 (some 246)) = d5301 p := by
  change (if p 162 then d2234 (change p 224 (some 246)) else d2304 (change p 224 (some 246))) = d5301 p
  rw [sub8253, sub8326]
  rfl
theorem sub8328 (p : Pattern) : d2306 (change p 224 (some 246)) = d5308 p := by
  change (if p 161 then d2242 (change p 224 (some 246)) else d2305 (change p 224 (some 246))) = d5308 p
  rw [sub8264, sub8327]
  rfl
theorem sub8329 (p : Pattern) : d2307 (change p 224 (some 246)) = d5319 p := by
  change (if p 160 then d2253 (change p 224 (some 246)) else d2306 (change p 224 (some 246))) = d5319 p
  rw [sub8275, sub8328]
  rfl
theorem sub8330 (p : Pattern) : d2308 (change p 224 (some 246)) = d5320 p := by
  change (if p 141 then d2307 (change p 224 (some 246)) else d2303 (change p 224 (some 246))) = d5320 p
  rw [sub8329, sub8325]
  rfl
theorem sub8331 (p : Pattern) : d2309 (change p 224 (some 246)) = d5331 p := by
  change (if p 138 then d2270 (change p 224 (some 246)) else d2308 (change p 224 (some 246))) = d5331 p
  rw [sub8292, sub8330]
  rfl
theorem sub8332 (p : Pattern) : d2310 (change p 224 (some 246)) = d5340 p := by
  change (if p 138 then d2284 (change p 224 (some 246)) else d2270 (change p 224 (some 246))) = d5340 p
  rw [sub8306, sub8292]
  rfl
theorem sub8333 (p : Pattern) : d2311 (change p 224 (some 246)) = d5341 p := by
  change (if p 116 then d2310 (change p 224 (some 246)) else d2309 (change p 224 (some 246))) = d5341 p
  rw [sub8332, sub8331]
  rfl
theorem sub8334 (p : Pattern) : d2312 (change p 224 (some 246)) = d5297 p := by
  change (if p 160 then d2227 (change p 224 (some 246)) else d2274 (change p 224 (some 246))) = d5297 p
  rw [sub8246, sub8296]
  rfl
theorem sub8335 (p : Pattern) : d2313 (change p 224 (some 246)) = d5320 p := by
  change (if p 141 then d2291 (change p 224 (some 246)) else d2312 (change p 224 (some 246))) = d5320 p
  rw [sub8313, sub8334]
  rfl
theorem sub8336 (p : Pattern) : d2314 (change p 224 (some 246)) = d5331 p := by
  change (if p 138 then d2270 (change p 224 (some 246)) else d2313 (change p 224 (some 246))) = d5331 p
  rw [sub8292, sub8335]
  rfl
theorem sub8337 (p : Pattern) : d2315 (change p 224 (some 246)) = d5343 p := by
  change (if p 116 then d2294 (change p 224 (some 246)) else d2314 (change p 224 (some 246))) = d5343 p
  rw [sub8316, sub8336]
  rfl
theorem sub8338 (p : Pattern) : d2316 (change p 224 (some 246)) = d5344 p := by
  change (if p 115 then d2315 (change p 224 (some 246)) else d2311 (change p 224 (some 246))) = d5344 p
  rw [sub8337, sub8333]
  rfl
theorem sub8339 (p : Pattern) : d2317 (change p 224 (some 246)) = d5344 p := by
  change (if p 71 then d2316 (change p 224 (some 246)) else d2296 (change p 224 (some 246))) = d5344 p
  rw [sub8338, sub8318]
  simp only [ite_self]
theorem sub8340 (p : Pattern) : d1 (change p 224 (some 246)) = d1 p := by
  rfl
theorem sub8341 (p : Pattern) : d102 (change p 224 (some 246)) = d102 p := by
  change (if p 247 then d12 (change p 224 (some 246)) else d1 (change p 224 (some 246))) = d102 p
  rw [sub8185, sub8340]
  rfl
theorem sub8342 (p : Pattern) : d103 (change p 224 (some 246)) = d102 p := by
  change d102 (change p 224 (some 246)) = d102 p
  exact sub8341 p
theorem sub8343 (p : Pattern) : d2318 (change p 224 (some 246)) = d102 p := by
  change d103 (change p 224 (some 246)) = d102 p
  exact sub8342 p
theorem sub8344 (p : Pattern) : d2319 (change p 224 (some 246)) = d102 p := by
  change d103 (change p 224 (some 246)) = d102 p
  exact sub8342 p
theorem sub8345 (p : Pattern) : d2320 (change p 224 (some 246)) = d102 p := by
  change (if p 204 then d2319 (change p 224 (some 246)) else d2318 (change p 224 (some 246))) = d102 p
  rw [sub8344, sub8343]
  simp only [ite_self]
theorem sub8346 (p : Pattern) : d2321 (change p 224 (some 246)) = d5345 p := by
  change (if p 204 then d12 (change p 224 (some 246)) else d2319 (change p 224 (some 246))) = d5345 p
  rw [sub8185, sub8344]
  rfl
theorem sub8347 (p : Pattern) : d2322 (change p 224 (some 246)) = d5346 p := by
  change (if p 182 then d2321 (change p 224 (some 246)) else d2320 (change p 224 (some 246))) = d5346 p
  rw [sub8346, sub8345]
  rfl
theorem sub8348 (p : Pattern) : d2323 (change p 224 (some 246)) = d102 p := by
  change d103 (change p 224 (some 246)) = d102 p
  exact sub8342 p
theorem sub8349 (p : Pattern) : d2324 (change p 224 (some 246)) = d102 p := by
  change (if p 204 then d2319 (change p 224 (some 246)) else d2323 (change p 224 (some 246))) = d102 p
  rw [sub8344, sub8348]
  simp only [ite_self]
theorem sub8350 (p : Pattern) : d2325 (change p 224 (some 246)) = d5346 p := by
  change (if p 182 then d2321 (change p 224 (some 246)) else d2324 (change p 224 (some 246))) = d5346 p
  rw [sub8346, sub8349]
  rfl
theorem sub8351 (p : Pattern) : d2326 (change p 224 (some 246)) = d5346 p := by
  change (if p 163 then d2325 (change p 224 (some 246)) else d2322 (change p 224 (some 246))) = d5346 p
  rw [sub8350, sub8347]
  simp only [ite_self]
theorem sub8352 (p : Pattern) : d2327 (change p 224 (some 246)) = d5346 p := by
  change (if p 182 then d2321 (change p 224 (some 246)) else d2319 (change p 224 (some 246))) = d5346 p
  rw [sub8346, sub8344]
  rfl
theorem sub8353 (p : Pattern) : d5 (change p 224 (some 246)) = d5 p := by
  rfl
theorem sub8354 (p : Pattern) : d106 (change p 224 (some 246)) = d106 p := by
  change (if p 247 then d12 (change p 224 (some 246)) else d5 (change p 224 (some 246))) = d106 p
  rw [sub8185, sub8353]
  rfl
theorem sub8355 (p : Pattern) : d107 (change p 224 (some 246)) = d106 p := by
  change d106 (change p 224 (some 246)) = d106 p
  exact sub8354 p
theorem sub8356 (p : Pattern) : d2328 (change p 224 (some 246)) = d106 p := by
  change d107 (change p 224 (some 246)) = d106 p
  exact sub8355 p
theorem sub8357 (p : Pattern) : d2329 (change p 224 (some 246)) = d5347 p := by
  change (if p 204 then d12 (change p 224 (some 246)) else d2328 (change p 224 (some 246))) = d5347 p
  rw [sub8185, sub8356]
  rfl
theorem sub8358 (p : Pattern) : d2330 (change p 224 (some 246)) = d5348 p := by
  change (if p 182 then d2329 (change p 224 (some 246)) else d2328 (change p 224 (some 246))) = d5348 p
  rw [sub8357, sub8356]
  rfl
theorem sub8359 (p : Pattern) : d2331 (change p 224 (some 246)) = d5349 p := by
  change (if p 163 then d2330 (change p 224 (some 246)) else d2327 (change p 224 (some 246))) = d5349 p
  rw [sub8358, sub8352]
  rfl
theorem sub8360 (p : Pattern) : d2332 (change p 224 (some 246)) = d5350 p := by
  change (if p 162 then d2331 (change p 224 (some 246)) else d2326 (change p 224 (some 246))) = d5350 p
  rw [sub8359, sub8351]
  rfl
theorem sub8361 (p : Pattern) : d2333 (change p 224 (some 246)) = d5351 p := by
  change (if p 163 then d12 (change p 224 (some 246)) else d2238 (change p 224 (some 246))) = d5351 p
  rw [sub8185, sub8260]
  rfl
theorem sub8362 (p : Pattern) : d2334 (change p 224 (some 246)) = d5352 p := by
  change (if p 162 then d2333 (change p 224 (some 246)) else d2331 (change p 224 (some 246))) = d5352 p
  rw [sub8361, sub8359]
  rfl
theorem sub8363 (p : Pattern) : d2335 (change p 224 (some 246)) = d5353 p := by
  change (if p 161 then d2334 (change p 224 (some 246)) else d2332 (change p 224 (some 246))) = d5353 p
  rw [sub8362, sub8360]
  rfl
theorem sub8364 (p : Pattern) : d3 (change p 224 (some 246)) = d3 p := by
  rfl
theorem sub8365 (p : Pattern) : d115 (change p 224 (some 246)) = d115 p := by
  change (if p 247 then d12 (change p 224 (some 246)) else d3 (change p 224 (some 246))) = d115 p
  rw [sub8185, sub8364]
  rfl
theorem sub8366 (p : Pattern) : d116 (change p 224 (some 246)) = d115 p := by
  change d115 (change p 224 (some 246)) = d115 p
  exact sub8365 p
theorem sub8367 (p : Pattern) : d2336 (change p 224 (some 246)) = d115 p := by
  change d116 (change p 224 (some 246)) = d115 p
  exact sub8366 p
theorem sub8368 (p : Pattern) : d2337 (change p 224 (some 246)) = d5354 p := by
  change (if p 204 then d12 (change p 224 (some 246)) else d2336 (change p 224 (some 246))) = d5354 p
  rw [sub8185, sub8367]
  rfl
theorem sub8369 (p : Pattern) : d2338 (change p 224 (some 246)) = d5355 p := by
  change (if p 182 then d2337 (change p 224 (some 246)) else d2319 (change p 224 (some 246))) = d5355 p
  rw [sub8368, sub8344]
  rfl
theorem sub8370 (p : Pattern) : d7 (change p 224 (some 246)) = d7 p := by
  rfl
theorem sub8371 (p : Pattern) : d119 (change p 224 (some 246)) = d119 p := by
  change (if p 247 then d12 (change p 224 (some 246)) else d7 (change p 224 (some 246))) = d119 p
  rw [sub8185, sub8370]
  rfl
theorem sub8372 (p : Pattern) : d120 (change p 224 (some 246)) = d119 p := by
  change d119 (change p 224 (some 246)) = d119 p
  exact sub8371 p
theorem sub8373 (p : Pattern) : d2339 (change p 224 (some 246)) = d119 p := by
  change d120 (change p 224 (some 246)) = d119 p
  exact sub8372 p
theorem sub8374 (p : Pattern) : d2340 (change p 224 (some 246)) = d5356 p := by
  change (if p 204 then d12 (change p 224 (some 246)) else d2339 (change p 224 (some 246))) = d5356 p
  rw [sub8185, sub8373]
  rfl
theorem sub8375 (p : Pattern) : d2341 (change p 224 (some 246)) = d5357 p := by
  change (if p 182 then d2340 (change p 224 (some 246)) else d2319 (change p 224 (some 246))) = d5357 p
  rw [sub8374, sub8344]
  rfl
theorem sub8376 (p : Pattern) : d2342 (change p 224 (some 246)) = d5358 p := by
  change (if p 163 then d2341 (change p 224 (some 246)) else d2338 (change p 224 (some 246))) = d5358 p
  rw [sub8375, sub8369]
  rfl
theorem sub8377 (p : Pattern) : d2343 (change p 224 (some 246)) = d5359 p := by
  change (if p 182 then d12 (change p 224 (some 246)) else d2319 (change p 224 (some 246))) = d5359 p
  rw [sub8185, sub8344]
  rfl
theorem sub8378 (p : Pattern) : d2344 (change p 224 (some 246)) = d5360 p := by
  change (if p 182 then d12 (change p 224 (some 246)) else d2328 (change p 224 (some 246))) = d5360 p
  rw [sub8185, sub8356]
  rfl
theorem sub8379 (p : Pattern) : d2345 (change p 224 (some 246)) = d5361 p := by
  change (if p 163 then d2344 (change p 224 (some 246)) else d2343 (change p 224 (some 246))) = d5361 p
  rw [sub8378, sub8377]
  rfl
theorem sub8380 (p : Pattern) : d2346 (change p 224 (some 246)) = d5362 p := by
  change (if p 162 then d2345 (change p 224 (some 246)) else d2342 (change p 224 (some 246))) = d5362 p
  rw [sub8379, sub8376]
  rfl
theorem sub8381 (p : Pattern) : d2347 (change p 224 (some 246)) = d5363 p := by
  change (if p 163 then d12 (change p 224 (some 246)) else d2248 (change p 224 (some 246))) = d5363 p
  rw [sub8185, sub8270]
  rfl
theorem sub8382 (p : Pattern) : d2348 (change p 224 (some 246)) = d5364 p := by
  change (if p 162 then d2347 (change p 224 (some 246)) else d2345 (change p 224 (some 246))) = d5364 p
  rw [sub8381, sub8379]
  rfl
theorem sub8383 (p : Pattern) : d2349 (change p 224 (some 246)) = d5365 p := by
  change (if p 161 then d2348 (change p 224 (some 246)) else d2346 (change p 224 (some 246))) = d5365 p
  rw [sub8382, sub8380]
  rfl
theorem sub8384 (p : Pattern) : d2350 (change p 224 (some 246)) = d5366 p := by
  change (if p 160 then d2349 (change p 224 (some 246)) else d2335 (change p 224 (some 246))) = d5366 p
  rw [sub8383, sub8363]
  rfl
theorem sub8385 (p : Pattern) : d2351 (change p 224 (some 246)) = d102 p := by
  change d103 (change p 224 (some 246)) = d102 p
  exact sub8342 p
theorem sub8386 (p : Pattern) : d2352 (change p 224 (some 246)) = d102 p := by
  change (if p 204 then d2319 (change p 224 (some 246)) else d2351 (change p 224 (some 246))) = d102 p
  rw [sub8344, sub8385]
  simp only [ite_self]
theorem sub8387 (p : Pattern) : d2353 (change p 224 (some 246)) = d5346 p := by
  change (if p 182 then d2321 (change p 224 (some 246)) else d2352 (change p 224 (some 246))) = d5346 p
  rw [sub8346, sub8386]
  rfl
theorem sub8388 (p : Pattern) : d2354 (change p 224 (some 246)) = d5367 p := by
  change (if p 182 then d2337 (change p 224 (some 246)) else d2336 (change p 224 (some 246))) = d5367 p
  rw [sub8368, sub8367]
  rfl
theorem sub8389 (p : Pattern) : d2355 (change p 224 (some 246)) = d5368 p := by
  change (if p 163 then d2354 (change p 224 (some 246)) else d2353 (change p 224 (some 246))) = d5368 p
  rw [sub8388, sub8387]
  rfl
theorem sub8390 (p : Pattern) : d2356 (change p 224 (some 246)) = d5369 p := by
  change (if p 163 then d2238 (change p 224 (some 246)) else d2330 (change p 224 (some 246))) = d5369 p
  rw [sub8260, sub8358]
  rfl
theorem sub8391 (p : Pattern) : d2357 (change p 224 (some 246)) = d5370 p := by
  change (if p 162 then d2356 (change p 224 (some 246)) else d2355 (change p 224 (some 246))) = d5370 p
  rw [sub8390, sub8389]
  rfl
theorem sub8392 (p : Pattern) : d2358 (change p 224 (some 246)) = d5371 p := by
  change (if p 163 then d2240 (change p 224 (some 246)) else d2330 (change p 224 (some 246))) = d5371 p
  rw [sub8262, sub8358]
  rfl
theorem sub8393 (p : Pattern) : d2359 (change p 224 (some 246)) = d5372 p := by
  change (if p 162 then d12 (change p 224 (some 246)) else d2358 (change p 224 (some 246))) = d5372 p
  rw [sub8185, sub8392]
  rfl
theorem sub8394 (p : Pattern) : d2360 (change p 224 (some 246)) = d5373 p := by
  change (if p 161 then d2359 (change p 224 (some 246)) else d2357 (change p 224 (some 246))) = d5373 p
  rw [sub8393, sub8391]
  rfl
theorem sub8395 (p : Pattern) : d2361 (change p 224 (some 246)) = d5374 p := by
  change (if p 182 then d12 (change p 224 (some 246)) else d2336 (change p 224 (some 246))) = d5374 p
  rw [sub8185, sub8367]
  rfl
theorem sub8396 (p : Pattern) : d2362 (change p 224 (some 246)) = d5375 p := by
  change (if p 163 then d2361 (change p 224 (some 246)) else d2341 (change p 224 (some 246))) = d5375 p
  rw [sub8395, sub8375]
  rfl
theorem sub8397 (p : Pattern) : d2363 (change p 224 (some 246)) = d5376 p := by
  change (if p 163 then d2248 (change p 224 (some 246)) else d2344 (change p 224 (some 246))) = d5376 p
  rw [sub8270, sub8378]
  rfl
theorem sub8398 (p : Pattern) : d2364 (change p 224 (some 246)) = d5377 p := by
  change (if p 162 then d2363 (change p 224 (some 246)) else d2362 (change p 224 (some 246))) = d5377 p
  rw [sub8397, sub8396]
  rfl
theorem sub8399 (p : Pattern) : d2365 (change p 224 (some 246)) = d5378 p := by
  change (if p 163 then d2250 (change p 224 (some 246)) else d2344 (change p 224 (some 246))) = d5378 p
  rw [sub8272, sub8378]
  rfl
end NetHack.Sokoban22Refined85
