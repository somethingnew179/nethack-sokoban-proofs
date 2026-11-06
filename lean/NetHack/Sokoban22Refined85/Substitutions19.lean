/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions18
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2280 (p : Pattern) : d41 (change p 10000 (some 141)) = d41 p := by
  change (if p 204 then d12 (change p 10000 (some 141)) else d40 (change p 10000 (some 141))) = d41 p
  rw [sub2248, sub2279]
  rfl
theorem sub2281 (p : Pattern) : d62 (change p 10000 (some 141)) = d62 p := by
  change (if p 182 then d41 (change p 10000 (some 141)) else d40 (change p 10000 (some 141))) = d62 p
  rw [sub2280, sub2279]
  rfl
theorem sub2282 (p : Pattern) : d63 (change p 10000 (some 141)) = d63 p := by
  change (if p 163 then d12 (change p 10000 (some 141)) else d62 (change p 10000 (some 141))) = d63 p
  rw [sub2248, sub2281]
  rfl
theorem sub2283 (p : Pattern) : d64 (change p 10000 (some 141)) = d64 p := by
  change (if p 162 then d63 (change p 10000 (some 141)) else d61 (change p 10000 (some 141))) = d64 p
  rw [sub2282, sub2276]
  rfl
theorem sub2284 (p : Pattern) : d65 (change p 10000 (some 141)) = d65 p := by
  change (if p 161 then d64 (change p 10000 (some 141)) else d56 (change p 10000 (some 141))) = d65 p
  rw [sub2283, sub2270]
  rfl
theorem sub2285 (p : Pattern) : d6 (change p 10000 (some 141)) = d6 p := by
  rfl
theorem sub2286 (p : Pattern) : d34 (change p 10000 (some 141)) = d34 p := by
  change (if p 247 then d12 (change p 10000 (some 141)) else d6 (change p 10000 (some 141))) = d34 p
  rw [sub2248, sub2285]
  rfl
theorem sub2287 (p : Pattern) : d35 (change p 10000 (some 141)) = d35 p := by
  change (if p 246 then d34 (change p 10000 (some 141)) else d6 (change p 10000 (some 141))) = d35 p
  rw [sub2286, sub2285]
  rfl
theorem sub2288 (p : Pattern) : d36 (change p 10000 (some 141)) = d36 p := by
  change (if p 204 then d12 (change p 10000 (some 141)) else d35 (change p 10000 (some 141))) = d36 p
  rw [sub2248, sub2287]
  rfl
theorem sub2289 (p : Pattern) : d37 (change p 10000 (some 141)) = d37 p := by
  change (if p 182 then d36 (change p 10000 (some 141)) else d14 (change p 10000 (some 141))) = d37 p
  rw [sub2288, sub2250]
  rfl
theorem sub2290 (p : Pattern) : d66 (change p 10000 (some 141)) = d66 p := by
  change (if p 182 then d12 (change p 10000 (some 141)) else d31 (change p 10000 (some 141))) = d66 p
  rw [sub2248, sub2255]
  rfl
theorem sub2291 (p : Pattern) : d67 (change p 10000 (some 141)) = d67 p := by
  change (if p 163 then d66 (change p 10000 (some 141)) else d37 (change p 10000 (some 141))) = d67 p
  rw [sub2290, sub2289]
  rfl
theorem sub2292 (p : Pattern) : d43 (change p 10000 (some 141)) = d43 p := by
  change (if p 182 then d12 (change p 10000 (some 141)) else d18 (change p 10000 (some 141))) = d43 p
  rw [sub2248, sub2261]
  rfl
theorem sub2293 (p : Pattern) : d48 (change p 10000 (some 141)) = d48 p := by
  change (if p 182 then d12 (change p 10000 (some 141)) else d24 (change p 10000 (some 141))) = d48 p
  rw [sub2248, sub2266]
  rfl
theorem sub2294 (p : Pattern) : d68 (change p 10000 (some 141)) = d68 p := by
  change (if p 163 then d48 (change p 10000 (some 141)) else d43 (change p 10000 (some 141))) = d68 p
  rw [sub2293, sub2292]
  rfl
theorem sub2295 (p : Pattern) : d69 (change p 10000 (some 141)) = d69 p := by
  change (if p 162 then d68 (change p 10000 (some 141)) else d67 (change p 10000 (some 141))) = d69 p
  rw [sub2294, sub2291]
  rfl
theorem sub2296 (p : Pattern) : d70 (change p 10000 (some 141)) = d70 p := by
  change (if p 182 then d12 (change p 10000 (some 141)) else d58 (change p 10000 (some 141))) = d70 p
  rw [sub2248, sub2273]
  rfl
theorem sub2297 (p : Pattern) : d71 (change p 10000 (some 141)) = d71 p := by
  change (if p 163 then d70 (change p 10000 (some 141)) else d43 (change p 10000 (some 141))) = d71 p
  rw [sub2296, sub2292]
  rfl
theorem sub2298 (p : Pattern) : d72 (change p 10000 (some 141)) = d72 p := by
  change (if p 182 then d12 (change p 10000 (some 141)) else d40 (change p 10000 (some 141))) = d72 p
  rw [sub2248, sub2279]
  rfl
theorem sub2299 (p : Pattern) : d73 (change p 10000 (some 141)) = d73 p := by
  change (if p 163 then d12 (change p 10000 (some 141)) else d72 (change p 10000 (some 141))) = d73 p
  rw [sub2248, sub2298]
  rfl
theorem sub2300 (p : Pattern) : d74 (change p 10000 (some 141)) = d74 p := by
  change (if p 162 then d73 (change p 10000 (some 141)) else d71 (change p 10000 (some 141))) = d74 p
  rw [sub2299, sub2297]
  rfl
theorem sub2301 (p : Pattern) : d75 (change p 10000 (some 141)) = d75 p := by
  change (if p 161 then d74 (change p 10000 (some 141)) else d69 (change p 10000 (some 141))) = d75 p
  rw [sub2300, sub2295]
  rfl
theorem sub2302 (p : Pattern) : d76 (change p 10000 (some 141)) = d76 p := by
  change (if p 160 then d75 (change p 10000 (some 141)) else d65 (change p 10000 (some 141))) = d76 p
  rw [sub2301, sub2284]
  rfl
theorem sub2303 (p : Pattern) : d77 (change p 10000 (some 141)) = d76 p := by
  change d76 (change p 10000 (some 141)) = d76 p
  exact sub2302 p
theorem sub2304 (p : Pattern) : d78 (change p 10000 (some 141)) = d78 p := by
  change (if p 182 then d36 (change p 10000 (some 141)) else d35 (change p 10000 (some 141))) = d78 p
  rw [sub2288, sub2287]
  rfl
theorem sub2305 (p : Pattern) : d83 (change p 10000 (some 141)) = d83 p := by
  change (if p 163 then d12 (change p 10000 (some 141)) else d78 (change p 10000 (some 141))) = d83 p
  rw [sub2248, sub2304]
  rfl
theorem sub2306 (p : Pattern) : d84 (change p 10000 (some 141)) = d84 p := by
  change (if p 162 then d12 (change p 10000 (some 141)) else d83 (change p 10000 (some 141))) = d84 p
  rw [sub2248, sub2305]
  rfl
theorem sub2307 (p : Pattern) : d85 (change p 10000 (some 141)) = d85 p := by
  change (if p 161 then d12 (change p 10000 (some 141)) else d84 (change p 10000 (some 141))) = d85 p
  rw [sub2248, sub2306]
  rfl
theorem sub2308 (p : Pattern) : d86 (change p 10000 (some 141)) = d86 p := by
  change (if p 160 then d85 (change p 10000 (some 141)) else d65 (change p 10000 (some 141))) = d86 p
  rw [sub2307, sub2284]
  rfl
theorem sub2309 (p : Pattern) : d87 (change p 10000 (some 141)) = d86 p := by
  change d86 (change p 10000 (some 141)) = d86 p
  exact sub2308 p
theorem sub2310 (p : Pattern) : d88 (change p 10000 (some 141)) = d4078 p := by
  change (if p 138 then d87 (change p 10000 (some 141)) else d77 (change p 10000 (some 141))) = d4078 p
  rw [sub2309, sub2303]
  rfl
theorem sub2311 (p : Pattern) : d91 (change p 10000 (some 141)) = d91 p := by
  change (if p 162 then d12 (change p 10000 (some 141)) else d63 (change p 10000 (some 141))) = d91 p
  rw [sub2248, sub2282]
  rfl
theorem sub2312 (p : Pattern) : d93 (change p 10000 (some 141)) = d93 p := by
  change (if p 161 then d12 (change p 10000 (some 141)) else d91 (change p 10000 (some 141))) = d93 p
  rw [sub2248, sub2311]
  rfl
theorem sub2313 (p : Pattern) : d95 (change p 10000 (some 141)) = d95 p := by
  change (if p 160 then d12 (change p 10000 (some 141)) else d93 (change p 10000 (some 141))) = d95 p
  rw [sub2248, sub2312]
  rfl
theorem sub2314 (p : Pattern) : d96 (change p 10000 (some 141)) = d95 p := by
  change d95 (change p 10000 (some 141)) = d95 p
  exact sub2313 p
theorem sub2315 (p : Pattern) : d97 (change p 10000 (some 141)) = d4079 p := by
  change (if p 138 then d96 (change p 10000 (some 141)) else d87 (change p 10000 (some 141))) = d4079 p
  rw [sub2314, sub2309]
  rfl
theorem sub2316 (p : Pattern) : d98 (change p 10000 (some 141)) = d4080 p := by
  change (if p 116 then d97 (change p 10000 (some 141)) else d88 (change p 10000 (some 141))) = d4080 p
  rw [sub2315, sub2310]
  rfl
theorem sub2317 (p : Pattern) : d99 (change p 10000 (some 141)) = d4081 p := by
  change (if p 138 then d12 (change p 10000 (some 141)) else d87 (change p 10000 (some 141))) = d4081 p
  rw [sub2248, sub2309]
  rfl
theorem sub2318 (p : Pattern) : d100 (change p 10000 (some 141)) = d4082 p := by
  change (if p 116 then d99 (change p 10000 (some 141)) else d88 (change p 10000 (some 141))) = d4082 p
  rw [sub2317, sub2310]
  rfl
theorem sub2319 (p : Pattern) : d101 (change p 10000 (some 141)) = d4083 p := by
  change (if p 115 then d100 (change p 10000 (some 141)) else d98 (change p 10000 (some 141))) = d4083 p
  rw [sub2318, sub2316]
  rfl
theorem sub2320 (p : Pattern) : d1 (change p 10000 (some 141)) = d1 p := by
  rfl
theorem sub2321 (p : Pattern) : d102 (change p 10000 (some 141)) = d102 p := by
  change (if p 247 then d12 (change p 10000 (some 141)) else d1 (change p 10000 (some 141))) = d102 p
  rw [sub2248, sub2320]
  rfl
theorem sub2322 (p : Pattern) : d103 (change p 10000 (some 141)) = d103 p := by
  change (if p 246 then d102 (change p 10000 (some 141)) else d1 (change p 10000 (some 141))) = d103 p
  rw [sub2321, sub2320]
  rfl
theorem sub2323 (p : Pattern) : d104 (change p 10000 (some 141)) = d104 p := by
  change (if p 204 then d12 (change p 10000 (some 141)) else d103 (change p 10000 (some 141))) = d104 p
  rw [sub2248, sub2322]
  rfl
theorem sub2324 (p : Pattern) : d105 (change p 10000 (some 141)) = d105 p := by
  change (if p 182 then d104 (change p 10000 (some 141)) else d103 (change p 10000 (some 141))) = d105 p
  rw [sub2323, sub2322]
  rfl
theorem sub2325 (p : Pattern) : d3 (change p 10000 (some 141)) = d3 p := by
  rfl
theorem sub2326 (p : Pattern) : d115 (change p 10000 (some 141)) = d115 p := by
  change (if p 247 then d12 (change p 10000 (some 141)) else d3 (change p 10000 (some 141))) = d115 p
  rw [sub2248, sub2325]
  rfl
theorem sub2327 (p : Pattern) : d116 (change p 10000 (some 141)) = d116 p := by
  change (if p 246 then d115 (change p 10000 (some 141)) else d3 (change p 10000 (some 141))) = d116 p
  rw [sub2326, sub2325]
  rfl
theorem sub2328 (p : Pattern) : d117 (change p 10000 (some 141)) = d117 p := by
  change (if p 204 then d12 (change p 10000 (some 141)) else d116 (change p 10000 (some 141))) = d117 p
  rw [sub2248, sub2327]
  rfl
theorem sub2329 (p : Pattern) : d132 (change p 10000 (some 141)) = d132 p := by
  change (if p 182 then d117 (change p 10000 (some 141)) else d116 (change p 10000 (some 141))) = d132 p
  rw [sub2328, sub2327]
  rfl
theorem sub2330 (p : Pattern) : d133 (change p 10000 (some 141)) = d133 p := by
  change (if p 163 then d132 (change p 10000 (some 141)) else d105 (change p 10000 (some 141))) = d133 p
  rw [sub2329, sub2324]
  rfl
theorem sub2331 (p : Pattern) : d5 (change p 10000 (some 141)) = d5 p := by
  rfl
theorem sub2332 (p : Pattern) : d106 (change p 10000 (some 141)) = d106 p := by
  change (if p 247 then d12 (change p 10000 (some 141)) else d5 (change p 10000 (some 141))) = d106 p
  rw [sub2248, sub2331]
  rfl
theorem sub2333 (p : Pattern) : d107 (change p 10000 (some 141)) = d107 p := by
  change (if p 246 then d106 (change p 10000 (some 141)) else d5 (change p 10000 (some 141))) = d107 p
  rw [sub2332, sub2331]
  rfl
theorem sub2334 (p : Pattern) : d108 (change p 10000 (some 141)) = d108 p := by
  change (if p 204 then d12 (change p 10000 (some 141)) else d107 (change p 10000 (some 141))) = d108 p
  rw [sub2248, sub2333]
  rfl
theorem sub2335 (p : Pattern) : d109 (change p 10000 (some 141)) = d109 p := by
  change (if p 182 then d108 (change p 10000 (some 141)) else d107 (change p 10000 (some 141))) = d109 p
  rw [sub2334, sub2333]
  rfl
theorem sub2336 (p : Pattern) : d134 (change p 10000 (some 141)) = d134 p := by
  change (if p 163 then d60 (change p 10000 (some 141)) else d109 (change p 10000 (some 141))) = d134 p
  rw [sub2275, sub2335]
  rfl
theorem sub2337 (p : Pattern) : d135 (change p 10000 (some 141)) = d135 p := by
  change (if p 162 then d134 (change p 10000 (some 141)) else d133 (change p 10000 (some 141))) = d135 p
  rw [sub2336, sub2330]
  rfl
theorem sub2338 (p : Pattern) : d136 (change p 10000 (some 141)) = d136 p := by
  change (if p 163 then d62 (change p 10000 (some 141)) else d109 (change p 10000 (some 141))) = d136 p
  rw [sub2281, sub2335]
  rfl
theorem sub2339 (p : Pattern) : d137 (change p 10000 (some 141)) = d137 p := by
  change (if p 162 then d12 (change p 10000 (some 141)) else d136 (change p 10000 (some 141))) = d137 p
  rw [sub2248, sub2338]
  rfl
theorem sub2340 (p : Pattern) : d138 (change p 10000 (some 141)) = d138 p := by
  change (if p 161 then d137 (change p 10000 (some 141)) else d135 (change p 10000 (some 141))) = d138 p
  rw [sub2339, sub2337]
  rfl
theorem sub2341 (p : Pattern) : d7 (change p 10000 (some 141)) = d7 p := by
  rfl
theorem sub2342 (p : Pattern) : d119 (change p 10000 (some 141)) = d119 p := by
  change (if p 247 then d12 (change p 10000 (some 141)) else d7 (change p 10000 (some 141))) = d119 p
  rw [sub2248, sub2341]
  rfl
theorem sub2343 (p : Pattern) : d120 (change p 10000 (some 141)) = d120 p := by
  change (if p 246 then d119 (change p 10000 (some 141)) else d7 (change p 10000 (some 141))) = d120 p
  rw [sub2342, sub2341]
  rfl
theorem sub2344 (p : Pattern) : d121 (change p 10000 (some 141)) = d121 p := by
  change (if p 204 then d12 (change p 10000 (some 141)) else d120 (change p 10000 (some 141))) = d121 p
  rw [sub2248, sub2343]
  rfl
theorem sub2345 (p : Pattern) : d122 (change p 10000 (some 141)) = d122 p := by
  change (if p 182 then d121 (change p 10000 (some 141)) else d103 (change p 10000 (some 141))) = d122 p
  rw [sub2344, sub2322]
  rfl
theorem sub2346 (p : Pattern) : d139 (change p 10000 (some 141)) = d139 p := by
  change (if p 182 then d12 (change p 10000 (some 141)) else d116 (change p 10000 (some 141))) = d139 p
  rw [sub2248, sub2327]
  rfl
theorem sub2347 (p : Pattern) : d140 (change p 10000 (some 141)) = d140 p := by
  change (if p 163 then d139 (change p 10000 (some 141)) else d122 (change p 10000 (some 141))) = d140 p
  rw [sub2346, sub2345]
  rfl
theorem sub2348 (p : Pattern) : d125 (change p 10000 (some 141)) = d125 p := by
  change (if p 182 then d12 (change p 10000 (some 141)) else d107 (change p 10000 (some 141))) = d125 p
  rw [sub2248, sub2333]
  rfl
theorem sub2349 (p : Pattern) : d141 (change p 10000 (some 141)) = d141 p := by
  change (if p 163 then d70 (change p 10000 (some 141)) else d125 (change p 10000 (some 141))) = d141 p
  rw [sub2296, sub2348]
  rfl
theorem sub2350 (p : Pattern) : d142 (change p 10000 (some 141)) = d142 p := by
  change (if p 162 then d141 (change p 10000 (some 141)) else d140 (change p 10000 (some 141))) = d142 p
  rw [sub2349, sub2347]
  rfl
theorem sub2351 (p : Pattern) : d143 (change p 10000 (some 141)) = d143 p := by
  change (if p 163 then d72 (change p 10000 (some 141)) else d125 (change p 10000 (some 141))) = d143 p
  rw [sub2298, sub2348]
  rfl
theorem sub2352 (p : Pattern) : d144 (change p 10000 (some 141)) = d144 p := by
  change (if p 162 then d12 (change p 10000 (some 141)) else d143 (change p 10000 (some 141))) = d144 p
  rw [sub2248, sub2351]
  rfl
theorem sub2353 (p : Pattern) : d145 (change p 10000 (some 141)) = d145 p := by
  change (if p 161 then d144 (change p 10000 (some 141)) else d142 (change p 10000 (some 141))) = d145 p
  rw [sub2352, sub2350]
  rfl
theorem sub2354 (p : Pattern) : d146 (change p 10000 (some 141)) = d146 p := by
  change (if p 160 then d145 (change p 10000 (some 141)) else d138 (change p 10000 (some 141))) = d146 p
  rw [sub2353, sub2340]
  rfl
theorem sub2355 (p : Pattern) : d147 (change p 10000 (some 141)) = d146 p := by
  change d146 (change p 10000 (some 141)) = d146 p
  exact sub2354 p
theorem sub2356 (p : Pattern) : d148 (change p 10000 (some 141)) = d148 p := by
  change (if p 182 then d121 (change p 10000 (some 141)) else d120 (change p 10000 (some 141))) = d148 p
  rw [sub2344, sub2343]
  rfl
theorem sub2357 (p : Pattern) : d153 (change p 10000 (some 141)) = d153 p := by
  change (if p 163 then d12 (change p 10000 (some 141)) else d148 (change p 10000 (some 141))) = d153 p
  rw [sub2248, sub2356]
  rfl
theorem sub2358 (p : Pattern) : d154 (change p 10000 (some 141)) = d154 p := by
  change (if p 162 then d12 (change p 10000 (some 141)) else d153 (change p 10000 (some 141))) = d154 p
  rw [sub2248, sub2357]
  rfl
theorem sub2359 (p : Pattern) : d155 (change p 10000 (some 141)) = d155 p := by
  change (if p 161 then d12 (change p 10000 (some 141)) else d154 (change p 10000 (some 141))) = d155 p
  rw [sub2248, sub2358]
  rfl
theorem sub2360 (p : Pattern) : d156 (change p 10000 (some 141)) = d156 p := by
  change (if p 160 then d155 (change p 10000 (some 141)) else d138 (change p 10000 (some 141))) = d156 p
  rw [sub2359, sub2340]
  rfl
theorem sub2361 (p : Pattern) : d157 (change p 10000 (some 141)) = d156 p := by
  change d156 (change p 10000 (some 141)) = d156 p
  exact sub2360 p
theorem sub2362 (p : Pattern) : d158 (change p 10000 (some 141)) = d4084 p := by
  change (if p 138 then d157 (change p 10000 (some 141)) else d147 (change p 10000 (some 141))) = d4084 p
  rw [sub2361, sub2355]
  rfl
theorem sub2363 (p : Pattern) : d162 (change p 10000 (some 141)) = d12 p := by
  change d12 (change p 10000 (some 141)) = d12 p
  exact sub2248 p
theorem sub2364 (p : Pattern) : d163 (change p 10000 (some 141)) = d4085 p := by
  change (if p 138 then d162 (change p 10000 (some 141)) else d157 (change p 10000 (some 141))) = d4085 p
  rw [sub2363, sub2361]
  rfl
theorem sub2365 (p : Pattern) : d164 (change p 10000 (some 141)) = d4086 p := by
  change (if p 116 then d163 (change p 10000 (some 141)) else d158 (change p 10000 (some 141))) = d4086 p
  rw [sub2364, sub2362]
  rfl
theorem sub2366 (p : Pattern) : d165 (change p 10000 (some 141)) = d4085 p := by
  change (if p 138 then d12 (change p 10000 (some 141)) else d157 (change p 10000 (some 141))) = d4085 p
  rw [sub2248, sub2361]
  rfl
theorem sub2367 (p : Pattern) : d166 (change p 10000 (some 141)) = d4086 p := by
  change (if p 116 then d165 (change p 10000 (some 141)) else d158 (change p 10000 (some 141))) = d4086 p
  rw [sub2366, sub2362]
  rfl
theorem sub2368 (p : Pattern) : d167 (change p 10000 (some 141)) = d4086 p := by
  change (if p 115 then d166 (change p 10000 (some 141)) else d164 (change p 10000 (some 141))) = d4086 p
  rw [sub2367, sub2365]
  simp only [ite_self]
theorem sub2369 (p : Pattern) : d168 (change p 10000 (some 141)) = d4087 p := by
  change (if p 71 then d167 (change p 10000 (some 141)) else d101 (change p 10000 (some 141))) = d4087 p
  rw [sub2368, sub2319]
  rfl
theorem sub2370 (p : Pattern) : d169 (change p 10000 (some 141)) = d4088 p := by
  change (if p 49 then d168 (change p 10000 (some 141)) else d101 (change p 10000 (some 141))) = d4088 p
  rw [sub2369, sub2319]
  rfl
theorem sub2371 (p : Pattern) : d211 (change p 10000 (some 141)) = d211 p := by
  change (if p 163 then d12 (change p 10000 (some 141)) else d109 (change p 10000 (some 141))) = d211 p
  rw [sub2248, sub2335]
  rfl
theorem sub2372 (p : Pattern) : d212 (change p 10000 (some 141)) = d212 p := by
  change (if p 162 then d211 (change p 10000 (some 141)) else d133 (change p 10000 (some 141))) = d212 p
  rw [sub2371, sub2330]
  rfl
theorem sub2373 (p : Pattern) : d213 (change p 10000 (some 141)) = d213 p := by
  change (if p 162 then d12 (change p 10000 (some 141)) else d211 (change p 10000 (some 141))) = d213 p
  rw [sub2248, sub2371]
  rfl
theorem sub2374 (p : Pattern) : d214 (change p 10000 (some 141)) = d214 p := by
  change (if p 161 then d213 (change p 10000 (some 141)) else d212 (change p 10000 (some 141))) = d214 p
  rw [sub2373, sub2372]
  rfl
theorem sub2375 (p : Pattern) : d215 (change p 10000 (some 141)) = d215 p := by
  change (if p 163 then d12 (change p 10000 (some 141)) else d125 (change p 10000 (some 141))) = d215 p
  rw [sub2248, sub2348]
  rfl
theorem sub2376 (p : Pattern) : d216 (change p 10000 (some 141)) = d216 p := by
  change (if p 162 then d215 (change p 10000 (some 141)) else d140 (change p 10000 (some 141))) = d216 p
  rw [sub2375, sub2347]
  rfl
theorem sub2377 (p : Pattern) : d217 (change p 10000 (some 141)) = d217 p := by
  change (if p 162 then d12 (change p 10000 (some 141)) else d215 (change p 10000 (some 141))) = d217 p
  rw [sub2248, sub2375]
  rfl
theorem sub2378 (p : Pattern) : d218 (change p 10000 (some 141)) = d218 p := by
  change (if p 161 then d217 (change p 10000 (some 141)) else d216 (change p 10000 (some 141))) = d218 p
  rw [sub2377, sub2376]
  rfl
theorem sub2379 (p : Pattern) : d219 (change p 10000 (some 141)) = d219 p := by
  change (if p 160 then d218 (change p 10000 (some 141)) else d214 (change p 10000 (some 141))) = d219 p
  rw [sub2378, sub2374]
  rfl
theorem sub2380 (p : Pattern) : d220 (change p 10000 (some 141)) = d219 p := by
  change d219 (change p 10000 (some 141)) = d219 p
  exact sub2379 p
theorem sub2381 (p : Pattern) : d221 (change p 10000 (some 141)) = d221 p := by
  change (if p 160 then d155 (change p 10000 (some 141)) else d214 (change p 10000 (some 141))) = d221 p
  rw [sub2359, sub2374]
  rfl
theorem sub2382 (p : Pattern) : d222 (change p 10000 (some 141)) = d221 p := by
  change d221 (change p 10000 (some 141)) = d221 p
  exact sub2381 p
theorem sub2383 (p : Pattern) : d223 (change p 10000 (some 141)) = d4089 p := by
  change (if p 138 then d222 (change p 10000 (some 141)) else d220 (change p 10000 (some 141))) = d4089 p
  rw [sub2382, sub2380]
  rfl
theorem sub2384 (p : Pattern) : d224 (change p 10000 (some 141)) = d4090 p := by
  change (if p 138 then d162 (change p 10000 (some 141)) else d222 (change p 10000 (some 141))) = d4090 p
  rw [sub2363, sub2382]
  rfl
theorem sub2385 (p : Pattern) : d225 (change p 10000 (some 141)) = d4091 p := by
  change (if p 116 then d224 (change p 10000 (some 141)) else d223 (change p 10000 (some 141))) = d4091 p
  rw [sub2384, sub2383]
  rfl
theorem sub2386 (p : Pattern) : d268 (change p 10000 (some 141)) = d268 p := by
  change (if p 204 then d116 (change p 10000 (some 141)) else d103 (change p 10000 (some 141))) = d268 p
  rw [sub2327, sub2322]
  rfl
theorem sub2387 (p : Pattern) : d270 (change p 10000 (some 141)) = d270 p := by
  change (if p 182 then d121 (change p 10000 (some 141)) else d268 (change p 10000 (some 141))) = d270 p
  rw [sub2344, sub2386]
  rfl
theorem sub2388 (p : Pattern) : d282 (change p 10000 (some 141)) = d282 p := by
  change (if p 204 then d107 (change p 10000 (some 141)) else d116 (change p 10000 (some 141))) = d282 p
  rw [sub2333, sub2327]
  rfl
theorem sub2389 (p : Pattern) : d283 (change p 10000 (some 141)) = d283 p := by
  change (if p 182 then d12 (change p 10000 (some 141)) else d282 (change p 10000 (some 141))) = d283 p
  rw [sub2248, sub2388]
  rfl
theorem sub2390 (p : Pattern) : d284 (change p 10000 (some 141)) = d284 p := by
  change (if p 163 then d283 (change p 10000 (some 141)) else d270 (change p 10000 (some 141))) = d284 p
  rw [sub2389, sub2387]
  rfl
theorem sub2391 (p : Pattern) : d273 (change p 10000 (some 141)) = d273 p := by
  change (if p 204 then d120 (change p 10000 (some 141)) else d107 (change p 10000 (some 141))) = d273 p
  rw [sub2343, sub2333]
  rfl
theorem sub2392 (p : Pattern) : d274 (change p 10000 (some 141)) = d274 p := by
  change (if p 182 then d12 (change p 10000 (some 141)) else d273 (change p 10000 (some 141))) = d274 p
  rw [sub2248, sub2391]
  rfl
theorem sub2393 (p : Pattern) : d285 (change p 10000 (some 141)) = d285 p := by
  change (if p 163 then d12 (change p 10000 (some 141)) else d274 (change p 10000 (some 141))) = d285 p
  rw [sub2248, sub2392]
  rfl
theorem sub2394 (p : Pattern) : d286 (change p 10000 (some 141)) = d286 p := by
  change (if p 162 then d285 (change p 10000 (some 141)) else d284 (change p 10000 (some 141))) = d286 p
  rw [sub2393, sub2390]
  rfl
theorem sub2395 (p : Pattern) : d287 (change p 10000 (some 141)) = d287 p := by
  change (if p 162 then d12 (change p 10000 (some 141)) else d285 (change p 10000 (some 141))) = d287 p
  rw [sub2248, sub2393]
  rfl
theorem sub2396 (p : Pattern) : d288 (change p 10000 (some 141)) = d288 p := by
  change (if p 161 then d287 (change p 10000 (some 141)) else d286 (change p 10000 (some 141))) = d288 p
  rw [sub2395, sub2394]
  rfl
theorem sub2397 (p : Pattern) : d289 (change p 10000 (some 141)) = d289 p := by
  change (if p 160 then d288 (change p 10000 (some 141)) else d214 (change p 10000 (some 141))) = d289 p
  rw [sub2396, sub2374]
  rfl
theorem sub2398 (p : Pattern) : d290 (change p 10000 (some 141)) = d289 p := by
  change d289 (change p 10000 (some 141)) = d289 p
  exact sub2397 p
theorem sub2399 (p : Pattern) : d269 (change p 10000 (some 141)) = d269 p := by
  change (if p 182 then d117 (change p 10000 (some 141)) else d268 (change p 10000 (some 141))) = d269 p
  rw [sub2328, sub2386]
  rfl
end NetHack.Sokoban22Refined85
