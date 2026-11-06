/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes18
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d2280 (p : Pattern) : Int := if p 161 then d2279 p else d2278 p
theorem agree2280 (p q : Pattern) (h : Agree support p q) : d2280 p = d2280 q := by
  simp only [d2280, h 161 (by decide), agree2279 p q h, agree2278 p q h]
theorem nonnegative2280 (p : Pattern) : 0 ≤ d2280 p :=
  nonnegative_ite (p 161) (nonnegative2279 p) (nonnegative2278 p)
def d2281 (p : Pattern) : Int := if p 161 then d12 p else d2279 p
theorem agree2281 (p q : Pattern) (h : Agree support p q) : d2281 p = d2281 q := by
  simp only [d2281, h 161 (by decide), agree12 p q h, agree2279 p q h]
theorem nonnegative2281 (p : Pattern) : 0 ≤ d2281 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2279 p)
def d2282 (p : Pattern) : Int := if p 160 then d2281 p else d2280 p
theorem agree2282 (p q : Pattern) (h : Agree support p q) : d2282 p = d2282 q := by
  simp only [d2282, h 160 (by decide), agree2281 p q h, agree2280 p q h]
theorem nonnegative2282 (p : Pattern) : 0 ≤ d2282 p :=
  nonnegative_ite (p 160) (nonnegative2281 p) (nonnegative2280 p)
def d2283 (p : Pattern) : Int := if p 160 then d12 p else d2281 p
theorem agree2283 (p q : Pattern) (h : Agree support p q) : d2283 p = d2283 q := by
  simp only [d2283, h 160 (by decide), agree12 p q h, agree2281 p q h]
theorem nonnegative2283 (p : Pattern) : 0 ≤ d2283 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative2281 p)
def d2284 (p : Pattern) : Int := if p 141 then d2283 p else d2282 p
theorem agree2284 (p q : Pattern) (h : Agree support p q) : d2284 p = d2284 q := by
  simp only [d2284, h 141 (by decide), agree2283 p q h, agree2282 p q h]
theorem nonnegative2284 (p : Pattern) : 0 ≤ d2284 p :=
  nonnegative_ite (p 141) (nonnegative2283 p) (nonnegative2282 p)
def d2285 (p : Pattern) : Int := if p 138 then d2284 p else d2276 p
theorem agree2285 (p q : Pattern) (h : Agree support p q) : d2285 p = d2285 q := by
  simp only [d2285, h 138 (by decide), agree2284 p q h, agree2276 p q h]
theorem nonnegative2285 (p : Pattern) : 0 ≤ d2285 p :=
  nonnegative_ite (p 138) (nonnegative2284 p) (nonnegative2276 p)
def d2286 (p : Pattern) : Int := if p 116 then d2285 p else d2271 p
theorem agree2286 (p q : Pattern) (h : Agree support p q) : d2286 p = d2286 q := by
  simp only [d2286, h 116 (by decide), agree2285 p q h, agree2271 p q h]
theorem nonnegative2286 (p : Pattern) : 0 ≤ d2286 p :=
  nonnegative_ite (p 116) (nonnegative2285 p) (nonnegative2271 p)
def d2287 (p : Pattern) : Int := if p 163 then d2201 p else d2191 p
theorem agree2287 (p q : Pattern) (h : Agree support p q) : d2287 p = d2287 q := by
  simp only [d2287, h 163 (by decide), agree2201 p q h, agree2191 p q h]
theorem nonnegative2287 (p : Pattern) : 0 ≤ d2287 p :=
  nonnegative_ite (p 163) (nonnegative2201 p) (nonnegative2191 p)
def d2288 (p : Pattern) : Int := if p 162 then d2202 p else d2287 p
theorem agree2288 (p q : Pattern) (h : Agree support p q) : d2288 p = d2288 q := by
  simp only [d2288, h 162 (by decide), agree2202 p q h, agree2287 p q h]
theorem nonnegative2288 (p : Pattern) : 0 ≤ d2288 p :=
  nonnegative_ite (p 162) (nonnegative2202 p) (nonnegative2287 p)
def d2289 (p : Pattern) : Int := if p 161 then d2207 p else d2288 p
theorem agree2289 (p q : Pattern) (h : Agree support p q) : d2289 p = d2289 q := by
  simp only [d2289, h 161 (by decide), agree2207 p q h, agree2288 p q h]
theorem nonnegative2289 (p : Pattern) : 0 ≤ d2289 p :=
  nonnegative_ite (p 161) (nonnegative2207 p) (nonnegative2288 p)
def d2290 (p : Pattern) : Int := if p 160 then d2227 p else d2289 p
theorem agree2290 (p q : Pattern) (h : Agree support p q) : d2290 p = d2290 q := by
  simp only [d2290, h 160 (by decide), agree2227 p q h, agree2289 p q h]
theorem nonnegative2290 (p : Pattern) : 0 ≤ d2290 p :=
  nonnegative_ite (p 160) (nonnegative2227 p) (nonnegative2289 p)
def d2291 (p : Pattern) : Int := if p 160 then d2253 p else d2265 p
theorem agree2291 (p q : Pattern) (h : Agree support p q) : d2291 p = d2291 q := by
  simp only [d2291, h 160 (by decide), agree2253 p q h, agree2265 p q h]
theorem nonnegative2291 (p : Pattern) : 0 ≤ d2291 p :=
  nonnegative_ite (p 160) (nonnegative2253 p) (nonnegative2265 p)
def d2292 (p : Pattern) : Int := if p 141 then d2291 p else d2290 p
theorem agree2292 (p q : Pattern) (h : Agree support p q) : d2292 p = d2292 q := by
  simp only [d2292, h 141 (by decide), agree2291 p q h, agree2290 p q h]
theorem nonnegative2292 (p : Pattern) : 0 ≤ d2292 p :=
  nonnegative_ite (p 141) (nonnegative2291 p) (nonnegative2290 p)
def d2293 (p : Pattern) : Int := if p 138 then d2270 p else d2292 p
theorem agree2293 (p q : Pattern) (h : Agree support p q) : d2293 p = d2293 q := by
  simp only [d2293, h 138 (by decide), agree2270 p q h, agree2292 p q h]
theorem nonnegative2293 (p : Pattern) : 0 ≤ d2293 p :=
  nonnegative_ite (p 138) (nonnegative2270 p) (nonnegative2292 p)
def d2294 (p : Pattern) : Int := if p 138 then d12 p else d2270 p
theorem agree2294 (p q : Pattern) (h : Agree support p q) : d2294 p = d2294 q := by
  simp only [d2294, h 138 (by decide), agree12 p q h, agree2270 p q h]
theorem nonnegative2294 (p : Pattern) : 0 ≤ d2294 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative2270 p)
def d2295 (p : Pattern) : Int := if p 116 then d2294 p else d2293 p
theorem agree2295 (p q : Pattern) (h : Agree support p q) : d2295 p = d2295 q := by
  simp only [d2295, h 116 (by decide), agree2294 p q h, agree2293 p q h]
theorem nonnegative2295 (p : Pattern) : 0 ≤ d2295 p :=
  nonnegative_ite (p 116) (nonnegative2294 p) (nonnegative2293 p)
def d2296 (p : Pattern) : Int := if p 115 then d2295 p else d2286 p
theorem agree2296 (p q : Pattern) (h : Agree support p q) : d2296 p = d2296 q := by
  simp only [d2296, h 115 (by decide), agree2295 p q h, agree2286 p q h]
theorem nonnegative2296 (p : Pattern) : 0 ≤ d2296 p :=
  nonnegative_ite (p 115) (nonnegative2295 p) (nonnegative2286 p)
def d2297 (p : Pattern) : Int := if p 224 then d320 p else d14 p
theorem agree2297 (p q : Pattern) (h : Agree support p q) : d2297 p = d2297 q := by
  simp only [d2297, h 224 (by decide), agree320 p q h, agree14 p q h]
theorem nonnegative2297 (p : Pattern) : 0 ≤ d2297 p :=
  nonnegative_ite (p 224) (nonnegative320 p) (nonnegative14 p)
def d2298 (p : Pattern) : Int := if p 204 then d2185 p else d2297 p
theorem agree2298 (p q : Pattern) (h : Agree support p q) : d2298 p = d2298 q := by
  simp only [d2298, h 204 (by decide), agree2185 p q h, agree2297 p q h]
theorem nonnegative2298 (p : Pattern) : 0 ≤ d2298 p :=
  nonnegative_ite (p 204) (nonnegative2185 p) (nonnegative2297 p)
def d2299 (p : Pattern) : Int := if p 182 then d2187 p else d2298 p
theorem agree2299 (p q : Pattern) (h : Agree support p q) : d2299 p = d2299 q := by
  simp only [d2299, h 182 (by decide), agree2187 p q h, agree2298 p q h]
theorem nonnegative2299 (p : Pattern) : 0 ≤ d2299 p :=
  nonnegative_ite (p 182) (nonnegative2187 p) (nonnegative2298 p)
def d2300 (p : Pattern) : Int := if p 163 then d2195 p else d2299 p
theorem agree2300 (p q : Pattern) (h : Agree support p q) : d2300 p = d2300 q := by
  simp only [d2300, h 163 (by decide), agree2195 p q h, agree2299 p q h]
theorem nonnegative2300 (p : Pattern) : 0 ≤ d2300 p :=
  nonnegative_ite (p 163) (nonnegative2195 p) (nonnegative2299 p)
def d2301 (p : Pattern) : Int := if p 162 then d2202 p else d2300 p
theorem agree2301 (p q : Pattern) (h : Agree support p q) : d2301 p = d2301 q := by
  simp only [d2301, h 162 (by decide), agree2202 p q h, agree2300 p q h]
theorem nonnegative2301 (p : Pattern) : 0 ≤ d2301 p :=
  nonnegative_ite (p 162) (nonnegative2202 p) (nonnegative2300 p)
def d2302 (p : Pattern) : Int := if p 161 then d2207 p else d2301 p
theorem agree2302 (p q : Pattern) (h : Agree support p q) : d2302 p = d2302 q := by
  simp only [d2302, h 161 (by decide), agree2207 p q h, agree2301 p q h]
theorem nonnegative2302 (p : Pattern) : 0 ≤ d2302 p :=
  nonnegative_ite (p 161) (nonnegative2207 p) (nonnegative2301 p)
def d2303 (p : Pattern) : Int := if p 160 then d2227 p else d2302 p
theorem agree2303 (p q : Pattern) (h : Agree support p q) : d2303 p = d2303 q := by
  simp only [d2303, h 160 (by decide), agree2227 p q h, agree2302 p q h]
theorem nonnegative2303 (p : Pattern) : 0 ≤ d2303 p :=
  nonnegative_ite (p 160) (nonnegative2227 p) (nonnegative2302 p)
def d2304 (p : Pattern) : Int := if p 163 then d2232 p else d2191 p
theorem agree2304 (p q : Pattern) (h : Agree support p q) : d2304 p = d2304 q := by
  simp only [d2304, h 163 (by decide), agree2232 p q h, agree2191 p q h]
theorem nonnegative2304 (p : Pattern) : 0 ≤ d2304 p :=
  nonnegative_ite (p 163) (nonnegative2232 p) (nonnegative2191 p)
def d2305 (p : Pattern) : Int := if p 162 then d2234 p else d2304 p
theorem agree2305 (p q : Pattern) (h : Agree support p q) : d2305 p = d2305 q := by
  simp only [d2305, h 162 (by decide), agree2234 p q h, agree2304 p q h]
theorem nonnegative2305 (p : Pattern) : 0 ≤ d2305 p :=
  nonnegative_ite (p 162) (nonnegative2234 p) (nonnegative2304 p)
def d2306 (p : Pattern) : Int := if p 161 then d2242 p else d2305 p
theorem agree2306 (p q : Pattern) (h : Agree support p q) : d2306 p = d2306 q := by
  simp only [d2306, h 161 (by decide), agree2242 p q h, agree2305 p q h]
theorem nonnegative2306 (p : Pattern) : 0 ≤ d2306 p :=
  nonnegative_ite (p 161) (nonnegative2242 p) (nonnegative2305 p)
def d2307 (p : Pattern) : Int := if p 160 then d2253 p else d2306 p
theorem agree2307 (p q : Pattern) (h : Agree support p q) : d2307 p = d2307 q := by
  simp only [d2307, h 160 (by decide), agree2253 p q h, agree2306 p q h]
theorem nonnegative2307 (p : Pattern) : 0 ≤ d2307 p :=
  nonnegative_ite (p 160) (nonnegative2253 p) (nonnegative2306 p)
def d2308 (p : Pattern) : Int := if p 141 then d2307 p else d2303 p
theorem agree2308 (p q : Pattern) (h : Agree support p q) : d2308 p = d2308 q := by
  simp only [d2308, h 141 (by decide), agree2307 p q h, agree2303 p q h]
theorem nonnegative2308 (p : Pattern) : 0 ≤ d2308 p :=
  nonnegative_ite (p 141) (nonnegative2307 p) (nonnegative2303 p)
def d2309 (p : Pattern) : Int := if p 138 then d2270 p else d2308 p
theorem agree2309 (p q : Pattern) (h : Agree support p q) : d2309 p = d2309 q := by
  simp only [d2309, h 138 (by decide), agree2270 p q h, agree2308 p q h]
theorem nonnegative2309 (p : Pattern) : 0 ≤ d2309 p :=
  nonnegative_ite (p 138) (nonnegative2270 p) (nonnegative2308 p)
def d2310 (p : Pattern) : Int := if p 138 then d2284 p else d2270 p
theorem agree2310 (p q : Pattern) (h : Agree support p q) : d2310 p = d2310 q := by
  simp only [d2310, h 138 (by decide), agree2284 p q h, agree2270 p q h]
theorem nonnegative2310 (p : Pattern) : 0 ≤ d2310 p :=
  nonnegative_ite (p 138) (nonnegative2284 p) (nonnegative2270 p)
def d2311 (p : Pattern) : Int := if p 116 then d2310 p else d2309 p
theorem agree2311 (p q : Pattern) (h : Agree support p q) : d2311 p = d2311 q := by
  simp only [d2311, h 116 (by decide), agree2310 p q h, agree2309 p q h]
theorem nonnegative2311 (p : Pattern) : 0 ≤ d2311 p :=
  nonnegative_ite (p 116) (nonnegative2310 p) (nonnegative2309 p)
def d2312 (p : Pattern) : Int := if p 160 then d2227 p else d2274 p
theorem agree2312 (p q : Pattern) (h : Agree support p q) : d2312 p = d2312 q := by
  simp only [d2312, h 160 (by decide), agree2227 p q h, agree2274 p q h]
theorem nonnegative2312 (p : Pattern) : 0 ≤ d2312 p :=
  nonnegative_ite (p 160) (nonnegative2227 p) (nonnegative2274 p)
def d2313 (p : Pattern) : Int := if p 141 then d2291 p else d2312 p
theorem agree2313 (p q : Pattern) (h : Agree support p q) : d2313 p = d2313 q := by
  simp only [d2313, h 141 (by decide), agree2291 p q h, agree2312 p q h]
theorem nonnegative2313 (p : Pattern) : 0 ≤ d2313 p :=
  nonnegative_ite (p 141) (nonnegative2291 p) (nonnegative2312 p)
def d2314 (p : Pattern) : Int := if p 138 then d2270 p else d2313 p
theorem agree2314 (p q : Pattern) (h : Agree support p q) : d2314 p = d2314 q := by
  simp only [d2314, h 138 (by decide), agree2270 p q h, agree2313 p q h]
theorem nonnegative2314 (p : Pattern) : 0 ≤ d2314 p :=
  nonnegative_ite (p 138) (nonnegative2270 p) (nonnegative2313 p)
def d2315 (p : Pattern) : Int := if p 116 then d2294 p else d2314 p
theorem agree2315 (p q : Pattern) (h : Agree support p q) : d2315 p = d2315 q := by
  simp only [d2315, h 116 (by decide), agree2294 p q h, agree2314 p q h]
theorem nonnegative2315 (p : Pattern) : 0 ≤ d2315 p :=
  nonnegative_ite (p 116) (nonnegative2294 p) (nonnegative2314 p)
def d2316 (p : Pattern) : Int := if p 115 then d2315 p else d2311 p
theorem agree2316 (p q : Pattern) (h : Agree support p q) : d2316 p = d2316 q := by
  simp only [d2316, h 115 (by decide), agree2315 p q h, agree2311 p q h]
theorem nonnegative2316 (p : Pattern) : 0 ≤ d2316 p :=
  nonnegative_ite (p 115) (nonnegative2315 p) (nonnegative2311 p)
def d2317 (p : Pattern) : Int := if p 71 then d2316 p else d2296 p
theorem agree2317 (p q : Pattern) (h : Agree support p q) : d2317 p = d2317 q := by
  simp only [d2317, h 71 (by decide), agree2316 p q h, agree2296 p q h]
theorem nonnegative2317 (p : Pattern) : 0 ≤ d2317 p :=
  nonnegative_ite (p 71) (nonnegative2316 p) (nonnegative2296 p)
def d2318 (p : Pattern) : Int := if p 224 then d320 p else d103 p
theorem agree2318 (p q : Pattern) (h : Agree support p q) : d2318 p = d2318 q := by
  simp only [d2318, h 224 (by decide), agree320 p q h, agree103 p q h]
theorem nonnegative2318 (p : Pattern) : 0 ≤ d2318 p :=
  nonnegative_ite (p 224) (nonnegative320 p) (nonnegative103 p)
def d2319 (p : Pattern) : Int := if p 224 then d12 p else d103 p
theorem agree2319 (p q : Pattern) (h : Agree support p q) : d2319 p = d2319 q := by
  simp only [d2319, h 224 (by decide), agree12 p q h, agree103 p q h]
theorem nonnegative2319 (p : Pattern) : 0 ≤ d2319 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative103 p)
def d2320 (p : Pattern) : Int := if p 204 then d2319 p else d2318 p
theorem agree2320 (p q : Pattern) (h : Agree support p q) : d2320 p = d2320 q := by
  simp only [d2320, h 204 (by decide), agree2319 p q h, agree2318 p q h]
theorem nonnegative2320 (p : Pattern) : 0 ≤ d2320 p :=
  nonnegative_ite (p 204) (nonnegative2319 p) (nonnegative2318 p)
def d2321 (p : Pattern) : Int := if p 204 then d12 p else d2319 p
theorem agree2321 (p q : Pattern) (h : Agree support p q) : d2321 p = d2321 q := by
  simp only [d2321, h 204 (by decide), agree12 p q h, agree2319 p q h]
theorem nonnegative2321 (p : Pattern) : 0 ≤ d2321 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2319 p)
def d2322 (p : Pattern) : Int := if p 182 then d2321 p else d2320 p
theorem agree2322 (p q : Pattern) (h : Agree support p q) : d2322 p = d2322 q := by
  simp only [d2322, h 182 (by decide), agree2321 p q h, agree2320 p q h]
theorem nonnegative2322 (p : Pattern) : 0 ≤ d2322 p :=
  nonnegative_ite (p 182) (nonnegative2321 p) (nonnegative2320 p)
def d2323 (p : Pattern) : Int := if p 224 then d332 p else d103 p
theorem agree2323 (p q : Pattern) (h : Agree support p q) : d2323 p = d2323 q := by
  simp only [d2323, h 224 (by decide), agree332 p q h, agree103 p q h]
theorem nonnegative2323 (p : Pattern) : 0 ≤ d2323 p :=
  nonnegative_ite (p 224) (nonnegative332 p) (nonnegative103 p)
def d2324 (p : Pattern) : Int := if p 204 then d2319 p else d2323 p
theorem agree2324 (p q : Pattern) (h : Agree support p q) : d2324 p = d2324 q := by
  simp only [d2324, h 204 (by decide), agree2319 p q h, agree2323 p q h]
theorem nonnegative2324 (p : Pattern) : 0 ≤ d2324 p :=
  nonnegative_ite (p 204) (nonnegative2319 p) (nonnegative2323 p)
def d2325 (p : Pattern) : Int := if p 182 then d2321 p else d2324 p
theorem agree2325 (p q : Pattern) (h : Agree support p q) : d2325 p = d2325 q := by
  simp only [d2325, h 182 (by decide), agree2321 p q h, agree2324 p q h]
theorem nonnegative2325 (p : Pattern) : 0 ≤ d2325 p :=
  nonnegative_ite (p 182) (nonnegative2321 p) (nonnegative2324 p)
def d2326 (p : Pattern) : Int := if p 163 then d2325 p else d2322 p
theorem agree2326 (p q : Pattern) (h : Agree support p q) : d2326 p = d2326 q := by
  simp only [d2326, h 163 (by decide), agree2325 p q h, agree2322 p q h]
theorem nonnegative2326 (p : Pattern) : 0 ≤ d2326 p :=
  nonnegative_ite (p 163) (nonnegative2325 p) (nonnegative2322 p)
def d2327 (p : Pattern) : Int := if p 182 then d2321 p else d2319 p
theorem agree2327 (p q : Pattern) (h : Agree support p q) : d2327 p = d2327 q := by
  simp only [d2327, h 182 (by decide), agree2321 p q h, agree2319 p q h]
theorem nonnegative2327 (p : Pattern) : 0 ≤ d2327 p :=
  nonnegative_ite (p 182) (nonnegative2321 p) (nonnegative2319 p)
def d2328 (p : Pattern) : Int := if p 224 then d12 p else d107 p
theorem agree2328 (p q : Pattern) (h : Agree support p q) : d2328 p = d2328 q := by
  simp only [d2328, h 224 (by decide), agree12 p q h, agree107 p q h]
theorem nonnegative2328 (p : Pattern) : 0 ≤ d2328 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative107 p)
def d2329 (p : Pattern) : Int := if p 204 then d12 p else d2328 p
theorem agree2329 (p q : Pattern) (h : Agree support p q) : d2329 p = d2329 q := by
  simp only [d2329, h 204 (by decide), agree12 p q h, agree2328 p q h]
theorem nonnegative2329 (p : Pattern) : 0 ≤ d2329 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2328 p)
def d2330 (p : Pattern) : Int := if p 182 then d2329 p else d2328 p
theorem agree2330 (p q : Pattern) (h : Agree support p q) : d2330 p = d2330 q := by
  simp only [d2330, h 182 (by decide), agree2329 p q h, agree2328 p q h]
theorem nonnegative2330 (p : Pattern) : 0 ≤ d2330 p :=
  nonnegative_ite (p 182) (nonnegative2329 p) (nonnegative2328 p)
def d2331 (p : Pattern) : Int := if p 163 then d2330 p else d2327 p
theorem agree2331 (p q : Pattern) (h : Agree support p q) : d2331 p = d2331 q := by
  simp only [d2331, h 163 (by decide), agree2330 p q h, agree2327 p q h]
theorem nonnegative2331 (p : Pattern) : 0 ≤ d2331 p :=
  nonnegative_ite (p 163) (nonnegative2330 p) (nonnegative2327 p)
def d2332 (p : Pattern) : Int := if p 162 then d2331 p else d2326 p
theorem agree2332 (p q : Pattern) (h : Agree support p q) : d2332 p = d2332 q := by
  simp only [d2332, h 162 (by decide), agree2331 p q h, agree2326 p q h]
theorem nonnegative2332 (p : Pattern) : 0 ≤ d2332 p :=
  nonnegative_ite (p 162) (nonnegative2331 p) (nonnegative2326 p)
def d2333 (p : Pattern) : Int := if p 163 then d12 p else d2238 p
theorem agree2333 (p q : Pattern) (h : Agree support p q) : d2333 p = d2333 q := by
  simp only [d2333, h 163 (by decide), agree12 p q h, agree2238 p q h]
theorem nonnegative2333 (p : Pattern) : 0 ≤ d2333 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2238 p)
def d2334 (p : Pattern) : Int := if p 162 then d2333 p else d2331 p
theorem agree2334 (p q : Pattern) (h : Agree support p q) : d2334 p = d2334 q := by
  simp only [d2334, h 162 (by decide), agree2333 p q h, agree2331 p q h]
theorem nonnegative2334 (p : Pattern) : 0 ≤ d2334 p :=
  nonnegative_ite (p 162) (nonnegative2333 p) (nonnegative2331 p)
def d2335 (p : Pattern) : Int := if p 161 then d2334 p else d2332 p
theorem agree2335 (p q : Pattern) (h : Agree support p q) : d2335 p = d2335 q := by
  simp only [d2335, h 161 (by decide), agree2334 p q h, agree2332 p q h]
theorem nonnegative2335 (p : Pattern) : 0 ≤ d2335 p :=
  nonnegative_ite (p 161) (nonnegative2334 p) (nonnegative2332 p)
def d2336 (p : Pattern) : Int := if p 224 then d12 p else d116 p
theorem agree2336 (p q : Pattern) (h : Agree support p q) : d2336 p = d2336 q := by
  simp only [d2336, h 224 (by decide), agree12 p q h, agree116 p q h]
theorem nonnegative2336 (p : Pattern) : 0 ≤ d2336 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative116 p)
def d2337 (p : Pattern) : Int := if p 204 then d12 p else d2336 p
theorem agree2337 (p q : Pattern) (h : Agree support p q) : d2337 p = d2337 q := by
  simp only [d2337, h 204 (by decide), agree12 p q h, agree2336 p q h]
theorem nonnegative2337 (p : Pattern) : 0 ≤ d2337 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2336 p)
def d2338 (p : Pattern) : Int := if p 182 then d2337 p else d2319 p
theorem agree2338 (p q : Pattern) (h : Agree support p q) : d2338 p = d2338 q := by
  simp only [d2338, h 182 (by decide), agree2337 p q h, agree2319 p q h]
theorem nonnegative2338 (p : Pattern) : 0 ≤ d2338 p :=
  nonnegative_ite (p 182) (nonnegative2337 p) (nonnegative2319 p)
def d2339 (p : Pattern) : Int := if p 224 then d12 p else d120 p
theorem agree2339 (p q : Pattern) (h : Agree support p q) : d2339 p = d2339 q := by
  simp only [d2339, h 224 (by decide), agree12 p q h, agree120 p q h]
theorem nonnegative2339 (p : Pattern) : 0 ≤ d2339 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative120 p)
def d2340 (p : Pattern) : Int := if p 204 then d12 p else d2339 p
theorem agree2340 (p q : Pattern) (h : Agree support p q) : d2340 p = d2340 q := by
  simp only [d2340, h 204 (by decide), agree12 p q h, agree2339 p q h]
theorem nonnegative2340 (p : Pattern) : 0 ≤ d2340 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2339 p)
def d2341 (p : Pattern) : Int := if p 182 then d2340 p else d2319 p
theorem agree2341 (p q : Pattern) (h : Agree support p q) : d2341 p = d2341 q := by
  simp only [d2341, h 182 (by decide), agree2340 p q h, agree2319 p q h]
theorem nonnegative2341 (p : Pattern) : 0 ≤ d2341 p :=
  nonnegative_ite (p 182) (nonnegative2340 p) (nonnegative2319 p)
def d2342 (p : Pattern) : Int := if p 163 then d2341 p else d2338 p
theorem agree2342 (p q : Pattern) (h : Agree support p q) : d2342 p = d2342 q := by
  simp only [d2342, h 163 (by decide), agree2341 p q h, agree2338 p q h]
theorem nonnegative2342 (p : Pattern) : 0 ≤ d2342 p :=
  nonnegative_ite (p 163) (nonnegative2341 p) (nonnegative2338 p)
def d2343 (p : Pattern) : Int := if p 182 then d12 p else d2319 p
theorem agree2343 (p q : Pattern) (h : Agree support p q) : d2343 p = d2343 q := by
  simp only [d2343, h 182 (by decide), agree12 p q h, agree2319 p q h]
theorem nonnegative2343 (p : Pattern) : 0 ≤ d2343 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2319 p)
def d2344 (p : Pattern) : Int := if p 182 then d12 p else d2328 p
theorem agree2344 (p q : Pattern) (h : Agree support p q) : d2344 p = d2344 q := by
  simp only [d2344, h 182 (by decide), agree12 p q h, agree2328 p q h]
theorem nonnegative2344 (p : Pattern) : 0 ≤ d2344 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2328 p)
def d2345 (p : Pattern) : Int := if p 163 then d2344 p else d2343 p
theorem agree2345 (p q : Pattern) (h : Agree support p q) : d2345 p = d2345 q := by
  simp only [d2345, h 163 (by decide), agree2344 p q h, agree2343 p q h]
theorem nonnegative2345 (p : Pattern) : 0 ≤ d2345 p :=
  nonnegative_ite (p 163) (nonnegative2344 p) (nonnegative2343 p)
def d2346 (p : Pattern) : Int := if p 162 then d2345 p else d2342 p
theorem agree2346 (p q : Pattern) (h : Agree support p q) : d2346 p = d2346 q := by
  simp only [d2346, h 162 (by decide), agree2345 p q h, agree2342 p q h]
theorem nonnegative2346 (p : Pattern) : 0 ≤ d2346 p :=
  nonnegative_ite (p 162) (nonnegative2345 p) (nonnegative2342 p)
def d2347 (p : Pattern) : Int := if p 163 then d12 p else d2248 p
theorem agree2347 (p q : Pattern) (h : Agree support p q) : d2347 p = d2347 q := by
  simp only [d2347, h 163 (by decide), agree12 p q h, agree2248 p q h]
theorem nonnegative2347 (p : Pattern) : 0 ≤ d2347 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2248 p)
def d2348 (p : Pattern) : Int := if p 162 then d2347 p else d2345 p
theorem agree2348 (p q : Pattern) (h : Agree support p q) : d2348 p = d2348 q := by
  simp only [d2348, h 162 (by decide), agree2347 p q h, agree2345 p q h]
theorem nonnegative2348 (p : Pattern) : 0 ≤ d2348 p :=
  nonnegative_ite (p 162) (nonnegative2347 p) (nonnegative2345 p)
def d2349 (p : Pattern) : Int := if p 161 then d2348 p else d2346 p
theorem agree2349 (p q : Pattern) (h : Agree support p q) : d2349 p = d2349 q := by
  simp only [d2349, h 161 (by decide), agree2348 p q h, agree2346 p q h]
theorem nonnegative2349 (p : Pattern) : 0 ≤ d2349 p :=
  nonnegative_ite (p 161) (nonnegative2348 p) (nonnegative2346 p)
def d2350 (p : Pattern) : Int := if p 160 then d2349 p else d2335 p
theorem agree2350 (p q : Pattern) (h : Agree support p q) : d2350 p = d2350 q := by
  simp only [d2350, h 160 (by decide), agree2349 p q h, agree2335 p q h]
theorem nonnegative2350 (p : Pattern) : 0 ≤ d2350 p :=
  nonnegative_ite (p 160) (nonnegative2349 p) (nonnegative2335 p)
def d2351 (p : Pattern) : Int := if p 224 then d330 p else d103 p
theorem agree2351 (p q : Pattern) (h : Agree support p q) : d2351 p = d2351 q := by
  simp only [d2351, h 224 (by decide), agree330 p q h, agree103 p q h]
theorem nonnegative2351 (p : Pattern) : 0 ≤ d2351 p :=
  nonnegative_ite (p 224) (nonnegative330 p) (nonnegative103 p)
def d2352 (p : Pattern) : Int := if p 204 then d2319 p else d2351 p
theorem agree2352 (p q : Pattern) (h : Agree support p q) : d2352 p = d2352 q := by
  simp only [d2352, h 204 (by decide), agree2319 p q h, agree2351 p q h]
theorem nonnegative2352 (p : Pattern) : 0 ≤ d2352 p :=
  nonnegative_ite (p 204) (nonnegative2319 p) (nonnegative2351 p)
def d2353 (p : Pattern) : Int := if p 182 then d2321 p else d2352 p
theorem agree2353 (p q : Pattern) (h : Agree support p q) : d2353 p = d2353 q := by
  simp only [d2353, h 182 (by decide), agree2321 p q h, agree2352 p q h]
theorem nonnegative2353 (p : Pattern) : 0 ≤ d2353 p :=
  nonnegative_ite (p 182) (nonnegative2321 p) (nonnegative2352 p)
def d2354 (p : Pattern) : Int := if p 182 then d2337 p else d2336 p
theorem agree2354 (p q : Pattern) (h : Agree support p q) : d2354 p = d2354 q := by
  simp only [d2354, h 182 (by decide), agree2337 p q h, agree2336 p q h]
theorem nonnegative2354 (p : Pattern) : 0 ≤ d2354 p :=
  nonnegative_ite (p 182) (nonnegative2337 p) (nonnegative2336 p)
def d2355 (p : Pattern) : Int := if p 163 then d2354 p else d2353 p
theorem agree2355 (p q : Pattern) (h : Agree support p q) : d2355 p = d2355 q := by
  simp only [d2355, h 163 (by decide), agree2354 p q h, agree2353 p q h]
theorem nonnegative2355 (p : Pattern) : 0 ≤ d2355 p :=
  nonnegative_ite (p 163) (nonnegative2354 p) (nonnegative2353 p)
def d2356 (p : Pattern) : Int := if p 163 then d2238 p else d2330 p
theorem agree2356 (p q : Pattern) (h : Agree support p q) : d2356 p = d2356 q := by
  simp only [d2356, h 163 (by decide), agree2238 p q h, agree2330 p q h]
theorem nonnegative2356 (p : Pattern) : 0 ≤ d2356 p :=
  nonnegative_ite (p 163) (nonnegative2238 p) (nonnegative2330 p)
def d2357 (p : Pattern) : Int := if p 162 then d2356 p else d2355 p
theorem agree2357 (p q : Pattern) (h : Agree support p q) : d2357 p = d2357 q := by
  simp only [d2357, h 162 (by decide), agree2356 p q h, agree2355 p q h]
theorem nonnegative2357 (p : Pattern) : 0 ≤ d2357 p :=
  nonnegative_ite (p 162) (nonnegative2356 p) (nonnegative2355 p)
def d2358 (p : Pattern) : Int := if p 163 then d2240 p else d2330 p
theorem agree2358 (p q : Pattern) (h : Agree support p q) : d2358 p = d2358 q := by
  simp only [d2358, h 163 (by decide), agree2240 p q h, agree2330 p q h]
theorem nonnegative2358 (p : Pattern) : 0 ≤ d2358 p :=
  nonnegative_ite (p 163) (nonnegative2240 p) (nonnegative2330 p)
def d2359 (p : Pattern) : Int := if p 162 then d12 p else d2358 p
theorem agree2359 (p q : Pattern) (h : Agree support p q) : d2359 p = d2359 q := by
  simp only [d2359, h 162 (by decide), agree12 p q h, agree2358 p q h]
theorem nonnegative2359 (p : Pattern) : 0 ≤ d2359 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2358 p)
def d2360 (p : Pattern) : Int := if p 161 then d2359 p else d2357 p
theorem agree2360 (p q : Pattern) (h : Agree support p q) : d2360 p = d2360 q := by
  simp only [d2360, h 161 (by decide), agree2359 p q h, agree2357 p q h]
theorem nonnegative2360 (p : Pattern) : 0 ≤ d2360 p :=
  nonnegative_ite (p 161) (nonnegative2359 p) (nonnegative2357 p)
def d2361 (p : Pattern) : Int := if p 182 then d12 p else d2336 p
theorem agree2361 (p q : Pattern) (h : Agree support p q) : d2361 p = d2361 q := by
  simp only [d2361, h 182 (by decide), agree12 p q h, agree2336 p q h]
theorem nonnegative2361 (p : Pattern) : 0 ≤ d2361 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2336 p)
def d2362 (p : Pattern) : Int := if p 163 then d2361 p else d2341 p
theorem agree2362 (p q : Pattern) (h : Agree support p q) : d2362 p = d2362 q := by
  simp only [d2362, h 163 (by decide), agree2361 p q h, agree2341 p q h]
theorem nonnegative2362 (p : Pattern) : 0 ≤ d2362 p :=
  nonnegative_ite (p 163) (nonnegative2361 p) (nonnegative2341 p)
def d2363 (p : Pattern) : Int := if p 163 then d2248 p else d2344 p
theorem agree2363 (p q : Pattern) (h : Agree support p q) : d2363 p = d2363 q := by
  simp only [d2363, h 163 (by decide), agree2248 p q h, agree2344 p q h]
theorem nonnegative2363 (p : Pattern) : 0 ≤ d2363 p :=
  nonnegative_ite (p 163) (nonnegative2248 p) (nonnegative2344 p)
def d2364 (p : Pattern) : Int := if p 162 then d2363 p else d2362 p
theorem agree2364 (p q : Pattern) (h : Agree support p q) : d2364 p = d2364 q := by
  simp only [d2364, h 162 (by decide), agree2363 p q h, agree2362 p q h]
theorem nonnegative2364 (p : Pattern) : 0 ≤ d2364 p :=
  nonnegative_ite (p 162) (nonnegative2363 p) (nonnegative2362 p)
def d2365 (p : Pattern) : Int := if p 163 then d2250 p else d2344 p
theorem agree2365 (p q : Pattern) (h : Agree support p q) : d2365 p = d2365 q := by
  simp only [d2365, h 163 (by decide), agree2250 p q h, agree2344 p q h]
theorem nonnegative2365 (p : Pattern) : 0 ≤ d2365 p :=
  nonnegative_ite (p 163) (nonnegative2250 p) (nonnegative2344 p)
def d2366 (p : Pattern) : Int := if p 162 then d12 p else d2365 p
theorem agree2366 (p q : Pattern) (h : Agree support p q) : d2366 p = d2366 q := by
  simp only [d2366, h 162 (by decide), agree12 p q h, agree2365 p q h]
theorem nonnegative2366 (p : Pattern) : 0 ≤ d2366 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2365 p)
def d2367 (p : Pattern) : Int := if p 161 then d2366 p else d2364 p
theorem agree2367 (p q : Pattern) (h : Agree support p q) : d2367 p = d2367 q := by
  simp only [d2367, h 161 (by decide), agree2366 p q h, agree2364 p q h]
theorem nonnegative2367 (p : Pattern) : 0 ≤ d2367 p :=
  nonnegative_ite (p 161) (nonnegative2366 p) (nonnegative2364 p)
def d2368 (p : Pattern) : Int := if p 160 then d2367 p else d2360 p
theorem agree2368 (p q : Pattern) (h : Agree support p q) : d2368 p = d2368 q := by
  simp only [d2368, h 160 (by decide), agree2367 p q h, agree2360 p q h]
theorem nonnegative2368 (p : Pattern) : 0 ≤ d2368 p :=
  nonnegative_ite (p 160) (nonnegative2367 p) (nonnegative2360 p)
def d2369 (p : Pattern) : Int := if p 141 then d2368 p else d2350 p
theorem agree2369 (p q : Pattern) (h : Agree support p q) : d2369 p = d2369 q := by
  simp only [d2369, h 141 (by decide), agree2368 p q h, agree2350 p q h]
theorem nonnegative2369 (p : Pattern) : 0 ≤ d2369 p :=
  nonnegative_ite (p 141) (nonnegative2368 p) (nonnegative2350 p)
def d2370 (p : Pattern) : Int := if p 162 then d2331 p else d2327 p
theorem agree2370 (p q : Pattern) (h : Agree support p q) : d2370 p = d2370 q := by
  simp only [d2370, h 162 (by decide), agree2331 p q h, agree2327 p q h]
theorem nonnegative2370 (p : Pattern) : 0 ≤ d2370 p :=
  nonnegative_ite (p 162) (nonnegative2331 p) (nonnegative2327 p)
def d2371 (p : Pattern) : Int := if p 161 then d2334 p else d2370 p
theorem agree2371 (p q : Pattern) (h : Agree support p q) : d2371 p = d2371 q := by
  simp only [d2371, h 161 (by decide), agree2334 p q h, agree2370 p q h]
theorem nonnegative2371 (p : Pattern) : 0 ≤ d2371 p :=
  nonnegative_ite (p 161) (nonnegative2334 p) (nonnegative2370 p)
def d2372 (p : Pattern) : Int := if p 182 then d2340 p else d2339 p
theorem agree2372 (p q : Pattern) (h : Agree support p q) : d2372 p = d2372 q := by
  simp only [d2372, h 182 (by decide), agree2340 p q h, agree2339 p q h]
theorem nonnegative2372 (p : Pattern) : 0 ≤ d2372 p :=
  nonnegative_ite (p 182) (nonnegative2340 p) (nonnegative2339 p)
def d2373 (p : Pattern) : Int := if p 163 then d2372 p else d2354 p
theorem agree2373 (p q : Pattern) (h : Agree support p q) : d2373 p = d2373 q := by
  simp only [d2373, h 163 (by decide), agree2372 p q h, agree2354 p q h]
theorem nonnegative2373 (p : Pattern) : 0 ≤ d2373 p :=
  nonnegative_ite (p 163) (nonnegative2372 p) (nonnegative2354 p)
def d2374 (p : Pattern) : Int := if p 162 then d12 p else d2373 p
theorem agree2374 (p q : Pattern) (h : Agree support p q) : d2374 p = d2374 q := by
  simp only [d2374, h 162 (by decide), agree12 p q h, agree2373 p q h]
theorem nonnegative2374 (p : Pattern) : 0 ≤ d2374 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2373 p)
def d2375 (p : Pattern) : Int := if p 161 then d12 p else d2374 p
theorem agree2375 (p q : Pattern) (h : Agree support p q) : d2375 p = d2375 q := by
  simp only [d2375, h 161 (by decide), agree12 p q h, agree2374 p q h]
theorem nonnegative2375 (p : Pattern) : 0 ≤ d2375 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2374 p)
def d2376 (p : Pattern) : Int := if p 160 then d2375 p else d2371 p
theorem agree2376 (p q : Pattern) (h : Agree support p q) : d2376 p = d2376 q := by
  simp only [d2376, h 160 (by decide), agree2375 p q h, agree2371 p q h]
theorem nonnegative2376 (p : Pattern) : 0 ≤ d2376 p :=
  nonnegative_ite (p 160) (nonnegative2375 p) (nonnegative2371 p)
def d2377 (p : Pattern) : Int := if p 163 then d2354 p else d2327 p
theorem agree2377 (p q : Pattern) (h : Agree support p q) : d2377 p = d2377 q := by
  simp only [d2377, h 163 (by decide), agree2354 p q h, agree2327 p q h]
theorem nonnegative2377 (p : Pattern) : 0 ≤ d2377 p :=
  nonnegative_ite (p 163) (nonnegative2354 p) (nonnegative2327 p)
def d2378 (p : Pattern) : Int := if p 162 then d2356 p else d2377 p
theorem agree2378 (p q : Pattern) (h : Agree support p q) : d2378 p = d2378 q := by
  simp only [d2378, h 162 (by decide), agree2356 p q h, agree2377 p q h]
theorem nonnegative2378 (p : Pattern) : 0 ≤ d2378 p :=
  nonnegative_ite (p 162) (nonnegative2356 p) (nonnegative2377 p)
def d2379 (p : Pattern) : Int := if p 161 then d2359 p else d2378 p
theorem agree2379 (p q : Pattern) (h : Agree support p q) : d2379 p = d2379 q := by
  simp only [d2379, h 161 (by decide), agree2359 p q h, agree2378 p q h]
theorem nonnegative2379 (p : Pattern) : 0 ≤ d2379 p :=
  nonnegative_ite (p 161) (nonnegative2359 p) (nonnegative2378 p)
def d2380 (p : Pattern) : Int := if p 163 then d12 p else d2372 p
theorem agree2380 (p q : Pattern) (h : Agree support p q) : d2380 p = d2380 q := by
  simp only [d2380, h 163 (by decide), agree12 p q h, agree2372 p q h]
theorem nonnegative2380 (p : Pattern) : 0 ≤ d2380 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2372 p)
def d2381 (p : Pattern) : Int := if p 162 then d12 p else d2380 p
theorem agree2381 (p q : Pattern) (h : Agree support p q) : d2381 p = d2381 q := by
  simp only [d2381, h 162 (by decide), agree12 p q h, agree2380 p q h]
theorem nonnegative2381 (p : Pattern) : 0 ≤ d2381 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2380 p)
def d2382 (p : Pattern) : Int := if p 161 then d12 p else d2381 p
theorem agree2382 (p q : Pattern) (h : Agree support p q) : d2382 p = d2382 q := by
  simp only [d2382, h 161 (by decide), agree12 p q h, agree2381 p q h]
theorem nonnegative2382 (p : Pattern) : 0 ≤ d2382 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2381 p)
def d2383 (p : Pattern) : Int := if p 160 then d2382 p else d2379 p
theorem agree2383 (p q : Pattern) (h : Agree support p q) : d2383 p = d2383 q := by
  simp only [d2383, h 160 (by decide), agree2382 p q h, agree2379 p q h]
theorem nonnegative2383 (p : Pattern) : 0 ≤ d2383 p :=
  nonnegative_ite (p 160) (nonnegative2382 p) (nonnegative2379 p)
def d2384 (p : Pattern) : Int := if p 141 then d2383 p else d2376 p
theorem agree2384 (p q : Pattern) (h : Agree support p q) : d2384 p = d2384 q := by
  simp only [d2384, h 141 (by decide), agree2383 p q h, agree2376 p q h]
theorem nonnegative2384 (p : Pattern) : 0 ≤ d2384 p :=
  nonnegative_ite (p 141) (nonnegative2383 p) (nonnegative2376 p)
def d2385 (p : Pattern) : Int := if p 138 then d2384 p else d2369 p
theorem agree2385 (p q : Pattern) (h : Agree support p q) : d2385 p = d2385 q := by
  simp only [d2385, h 138 (by decide), agree2384 p q h, agree2369 p q h]
theorem nonnegative2385 (p : Pattern) : 0 ≤ d2385 p :=
  nonnegative_ite (p 138) (nonnegative2384 p) (nonnegative2369 p)
def d2386 (p : Pattern) : Int := if p 162 then d12 p else d2333 p
theorem agree2386 (p q : Pattern) (h : Agree support p q) : d2386 p = d2386 q := by
  simp only [d2386, h 162 (by decide), agree12 p q h, agree2333 p q h]
theorem nonnegative2386 (p : Pattern) : 0 ≤ d2386 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2333 p)
def d2387 (p : Pattern) : Int := if p 161 then d12 p else d2386 p
theorem agree2387 (p q : Pattern) (h : Agree support p q) : d2387 p = d2387 q := by
  simp only [d2387, h 161 (by decide), agree12 p q h, agree2386 p q h]
theorem nonnegative2387 (p : Pattern) : 0 ≤ d2387 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2386 p)
def d2388 (p : Pattern) : Int := if p 160 then d12 p else d2387 p
theorem agree2388 (p q : Pattern) (h : Agree support p q) : d2388 p = d2388 q := by
  simp only [d2388, h 160 (by decide), agree12 p q h, agree2387 p q h]
theorem nonnegative2388 (p : Pattern) : 0 ≤ d2388 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative2387 p)
def d2389 (p : Pattern) : Int := if p 141 then d12 p else d2388 p
theorem agree2389 (p q : Pattern) (h : Agree support p q) : d2389 p = d2389 q := by
  simp only [d2389, h 141 (by decide), agree12 p q h, agree2388 p q h]
theorem nonnegative2389 (p : Pattern) : 0 ≤ d2389 p :=
  nonnegative_ite (p 141) (nonnegative12 p) (nonnegative2388 p)
def d2390 (p : Pattern) : Int := if p 138 then d2389 p else d2384 p
theorem agree2390 (p q : Pattern) (h : Agree support p q) : d2390 p = d2390 q := by
  simp only [d2390, h 138 (by decide), agree2389 p q h, agree2384 p q h]
theorem nonnegative2390 (p : Pattern) : 0 ≤ d2390 p :=
  nonnegative_ite (p 138) (nonnegative2389 p) (nonnegative2384 p)
def d2391 (p : Pattern) : Int := if p 116 then d2390 p else d2385 p
theorem agree2391 (p q : Pattern) (h : Agree support p q) : d2391 p = d2391 q := by
  simp only [d2391, h 116 (by decide), agree2390 p q h, agree2385 p q h]
theorem nonnegative2391 (p : Pattern) : 0 ≤ d2391 p :=
  nonnegative_ite (p 116) (nonnegative2390 p) (nonnegative2385 p)
def d2392 (p : Pattern) : Int := if p 163 then d2327 p else d2325 p
theorem agree2392 (p q : Pattern) (h : Agree support p q) : d2392 p = d2392 q := by
  simp only [d2392, h 163 (by decide), agree2327 p q h, agree2325 p q h]
theorem nonnegative2392 (p : Pattern) : 0 ≤ d2392 p :=
  nonnegative_ite (p 163) (nonnegative2327 p) (nonnegative2325 p)
def d2393 (p : Pattern) : Int := if p 162 then d2331 p else d2392 p
theorem agree2393 (p q : Pattern) (h : Agree support p q) : d2393 p = d2393 q := by
  simp only [d2393, h 162 (by decide), agree2331 p q h, agree2392 p q h]
theorem nonnegative2393 (p : Pattern) : 0 ≤ d2393 p :=
  nonnegative_ite (p 162) (nonnegative2331 p) (nonnegative2392 p)
def d2394 (p : Pattern) : Int := if p 161 then d2334 p else d2393 p
theorem agree2394 (p q : Pattern) (h : Agree support p q) : d2394 p = d2394 q := by
  simp only [d2394, h 161 (by decide), agree2334 p q h, agree2393 p q h]
theorem nonnegative2394 (p : Pattern) : 0 ≤ d2394 p :=
  nonnegative_ite (p 161) (nonnegative2334 p) (nonnegative2393 p)
def d2395 (p : Pattern) : Int := if p 160 then d2349 p else d2394 p
theorem agree2395 (p q : Pattern) (h : Agree support p q) : d2395 p = d2395 q := by
  simp only [d2395, h 160 (by decide), agree2349 p q h, agree2394 p q h]
theorem nonnegative2395 (p : Pattern) : 0 ≤ d2395 p :=
  nonnegative_ite (p 160) (nonnegative2349 p) (nonnegative2394 p)
def d2396 (p : Pattern) : Int := if p 160 then d2367 p else d2379 p
theorem agree2396 (p q : Pattern) (h : Agree support p q) : d2396 p = d2396 q := by
  simp only [d2396, h 160 (by decide), agree2367 p q h, agree2379 p q h]
theorem nonnegative2396 (p : Pattern) : 0 ≤ d2396 p :=
  nonnegative_ite (p 160) (nonnegative2367 p) (nonnegative2379 p)
def d2397 (p : Pattern) : Int := if p 141 then d2396 p else d2395 p
theorem agree2397 (p q : Pattern) (h : Agree support p q) : d2397 p = d2397 q := by
  simp only [d2397, h 141 (by decide), agree2396 p q h, agree2395 p q h]
theorem nonnegative2397 (p : Pattern) : 0 ≤ d2397 p :=
  nonnegative_ite (p 141) (nonnegative2396 p) (nonnegative2395 p)
def d2398 (p : Pattern) : Int := if p 138 then d2384 p else d2397 p
theorem agree2398 (p q : Pattern) (h : Agree support p q) : d2398 p = d2398 q := by
  simp only [d2398, h 138 (by decide), agree2384 p q h, agree2397 p q h]
theorem nonnegative2398 (p : Pattern) : 0 ≤ d2398 p :=
  nonnegative_ite (p 138) (nonnegative2384 p) (nonnegative2397 p)
def d2399 (p : Pattern) : Int := if p 138 then d12 p else d2384 p
theorem agree2399 (p q : Pattern) (h : Agree support p q) : d2399 p = d2399 q := by
  simp only [d2399, h 138 (by decide), agree12 p q h, agree2384 p q h]
theorem nonnegative2399 (p : Pattern) : 0 ≤ d2399 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative2384 p)
end NetHack.Sokoban22Refined85
