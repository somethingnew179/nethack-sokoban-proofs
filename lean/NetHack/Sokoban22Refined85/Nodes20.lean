/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes19
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d2400 (p : Pattern) : Int := if p 116 then d2399 p else d2398 p
theorem agree2400 (p q : Pattern) (h : Agree support p q) : d2400 p = d2400 q := by
  simp only [d2400, h 116 (by decide), agree2399 p q h, agree2398 p q h]
theorem nonnegative2400 (p : Pattern) : 0 ≤ d2400 p :=
  nonnegative_ite (p 116) (nonnegative2399 p) (nonnegative2398 p)
def d2401 (p : Pattern) : Int := if p 115 then d2400 p else d2391 p
theorem agree2401 (p q : Pattern) (h : Agree support p q) : d2401 p = d2401 q := by
  simp only [d2401, h 115 (by decide), agree2400 p q h, agree2391 p q h]
theorem nonnegative2401 (p : Pattern) : 0 ≤ d2401 p :=
  nonnegative_ite (p 115) (nonnegative2400 p) (nonnegative2391 p)
def d2402 (p : Pattern) : Int := if p 71 then d2401 p else d2296 p
theorem agree2402 (p q : Pattern) (h : Agree support p q) : d2402 p = d2402 q := by
  simp only [d2402, h 71 (by decide), agree2401 p q h, agree2296 p q h]
theorem nonnegative2402 (p : Pattern) : 0 ≤ d2402 p :=
  nonnegative_ite (p 71) (nonnegative2401 p) (nonnegative2296 p)
def d2403 (p : Pattern) : Int := if p 49 then d2402 p else d2317 p
theorem agree2403 (p q : Pattern) (h : Agree support p q) : d2403 p = d2403 q := by
  simp only [d2403, h 49 (by decide), agree2402 p q h, agree2317 p q h]
theorem nonnegative2403 (p : Pattern) : 0 ≤ d2403 p :=
  nonnegative_ite (p 49) (nonnegative2402 p) (nonnegative2317 p)
def d2404 (p : Pattern) : Int := if p 182 then d2213 p else d2209 p
theorem agree2404 (p q : Pattern) (h : Agree support p q) : d2404 p = d2404 q := by
  simp only [d2404, h 182 (by decide), agree2213 p q h, agree2209 p q h]
theorem nonnegative2404 (p : Pattern) : 0 ≤ d2404 p :=
  nonnegative_ite (p 182) (nonnegative2213 p) (nonnegative2209 p)
def d2405 (p : Pattern) : Int := if p 163 then d2404 p else d2232 p
theorem agree2405 (p q : Pattern) (h : Agree support p q) : d2405 p = d2405 q := by
  simp only [d2405, h 163 (by decide), agree2404 p q h, agree2232 p q h]
theorem nonnegative2405 (p : Pattern) : 0 ≤ d2405 p :=
  nonnegative_ite (p 163) (nonnegative2404 p) (nonnegative2232 p)
def d2406 (p : Pattern) : Int := if p 182 then d2217 p else d2209 p
theorem agree2406 (p q : Pattern) (h : Agree support p q) : d2406 p = d2406 q := by
  simp only [d2406, h 182 (by decide), agree2217 p q h, agree2209 p q h]
theorem nonnegative2406 (p : Pattern) : 0 ≤ d2406 p :=
  nonnegative_ite (p 182) (nonnegative2217 p) (nonnegative2209 p)
def d2407 (p : Pattern) : Int := if p 182 then d12 p else d2212 p
theorem agree2407 (p q : Pattern) (h : Agree support p q) : d2407 p = d2407 q := by
  simp only [d2407, h 182 (by decide), agree12 p q h, agree2212 p q h]
theorem nonnegative2407 (p : Pattern) : 0 ≤ d2407 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2212 p)
def d2408 (p : Pattern) : Int := if p 163 then d2407 p else d2406 p
theorem agree2408 (p q : Pattern) (h : Agree support p q) : d2408 p = d2408 q := by
  simp only [d2408, h 163 (by decide), agree2407 p q h, agree2406 p q h]
theorem nonnegative2408 (p : Pattern) : 0 ≤ d2408 p :=
  nonnegative_ite (p 163) (nonnegative2407 p) (nonnegative2406 p)
def d2409 (p : Pattern) : Int := if p 162 then d2408 p else d2405 p
theorem agree2409 (p q : Pattern) (h : Agree support p q) : d2409 p = d2409 q := by
  simp only [d2409, h 162 (by decide), agree2408 p q h, agree2405 p q h]
theorem nonnegative2409 (p : Pattern) : 0 ≤ d2409 p :=
  nonnegative_ite (p 162) (nonnegative2408 p) (nonnegative2405 p)
def d2410 (p : Pattern) : Int := if p 163 then d2407 p else d2244 p
theorem agree2410 (p q : Pattern) (h : Agree support p q) : d2410 p = d2410 q := by
  simp only [d2410, h 163 (by decide), agree2407 p q h, agree2244 p q h]
theorem nonnegative2410 (p : Pattern) : 0 ≤ d2410 p :=
  nonnegative_ite (p 163) (nonnegative2407 p) (nonnegative2244 p)
def d2411 (p : Pattern) : Int := if p 162 then d2251 p else d2410 p
theorem agree2411 (p q : Pattern) (h : Agree support p q) : d2411 p = d2411 q := by
  simp only [d2411, h 162 (by decide), agree2251 p q h, agree2410 p q h]
theorem nonnegative2411 (p : Pattern) : 0 ≤ d2411 p :=
  nonnegative_ite (p 162) (nonnegative2251 p) (nonnegative2410 p)
def d2412 (p : Pattern) : Int := if p 161 then d2411 p else d2409 p
theorem agree2412 (p q : Pattern) (h : Agree support p q) : d2412 p = d2412 q := by
  simp only [d2412, h 161 (by decide), agree2411 p q h, agree2409 p q h]
theorem nonnegative2412 (p : Pattern) : 0 ≤ d2412 p :=
  nonnegative_ite (p 161) (nonnegative2411 p) (nonnegative2409 p)
def d2413 (p : Pattern) : Int := if p 160 then d2412 p else d2274 p
theorem agree2413 (p q : Pattern) (h : Agree support p q) : d2413 p = d2413 q := by
  simp only [d2413, h 160 (by decide), agree2412 p q h, agree2274 p q h]
theorem nonnegative2413 (p : Pattern) : 0 ≤ d2413 p :=
  nonnegative_ite (p 160) (nonnegative2412 p) (nonnegative2274 p)
def d2414 (p : Pattern) : Int := if p 163 then d2219 p else d2404 p
theorem agree2414 (p q : Pattern) (h : Agree support p q) : d2414 p = d2414 q := by
  simp only [d2414, h 163 (by decide), agree2219 p q h, agree2404 p q h]
theorem nonnegative2414 (p : Pattern) : 0 ≤ d2414 p :=
  nonnegative_ite (p 163) (nonnegative2219 p) (nonnegative2404 p)
def d2415 (p : Pattern) : Int := if p 163 then d2250 p else d2407 p
theorem agree2415 (p q : Pattern) (h : Agree support p q) : d2415 p = d2415 q := by
  simp only [d2415, h 163 (by decide), agree2250 p q h, agree2407 p q h]
theorem nonnegative2415 (p : Pattern) : 0 ≤ d2415 p :=
  nonnegative_ite (p 163) (nonnegative2250 p) (nonnegative2407 p)
def d2416 (p : Pattern) : Int := if p 162 then d2415 p else d2414 p
theorem agree2416 (p q : Pattern) (h : Agree support p q) : d2416 p = d2416 q := by
  simp only [d2416, h 162 (by decide), agree2415 p q h, agree2414 p q h]
theorem nonnegative2416 (p : Pattern) : 0 ≤ d2416 p :=
  nonnegative_ite (p 162) (nonnegative2415 p) (nonnegative2414 p)
def d2417 (p : Pattern) : Int := if p 163 then d12 p else d2407 p
theorem agree2417 (p q : Pattern) (h : Agree support p q) : d2417 p = d2417 q := by
  simp only [d2417, h 163 (by decide), agree12 p q h, agree2407 p q h]
theorem nonnegative2417 (p : Pattern) : 0 ≤ d2417 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2407 p)
def d2418 (p : Pattern) : Int := if p 162 then d12 p else d2417 p
theorem agree2418 (p q : Pattern) (h : Agree support p q) : d2418 p = d2418 q := by
  simp only [d2418, h 162 (by decide), agree12 p q h, agree2417 p q h]
theorem nonnegative2418 (p : Pattern) : 0 ≤ d2418 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2417 p)
def d2419 (p : Pattern) : Int := if p 161 then d2418 p else d2416 p
theorem agree2419 (p q : Pattern) (h : Agree support p q) : d2419 p = d2419 q := by
  simp only [d2419, h 161 (by decide), agree2418 p q h, agree2416 p q h]
theorem nonnegative2419 (p : Pattern) : 0 ≤ d2419 p :=
  nonnegative_ite (p 161) (nonnegative2418 p) (nonnegative2416 p)
def d2420 (p : Pattern) : Int := if p 160 then d2419 p else d2265 p
theorem agree2420 (p q : Pattern) (h : Agree support p q) : d2420 p = d2420 q := by
  simp only [d2420, h 160 (by decide), agree2419 p q h, agree2265 p q h]
theorem nonnegative2420 (p : Pattern) : 0 ≤ d2420 p :=
  nonnegative_ite (p 160) (nonnegative2419 p) (nonnegative2265 p)
def d2421 (p : Pattern) : Int := if p 141 then d2420 p else d2413 p
theorem agree2421 (p q : Pattern) (h : Agree support p q) : d2421 p = d2421 q := by
  simp only [d2421, h 141 (by decide), agree2420 p q h, agree2413 p q h]
theorem nonnegative2421 (p : Pattern) : 0 ≤ d2421 p :=
  nonnegative_ite (p 141) (nonnegative2420 p) (nonnegative2413 p)
def d2422 (p : Pattern) : Int := if p 162 then d2259 p else d2201 p
theorem agree2422 (p q : Pattern) (h : Agree support p q) : d2422 p = d2422 q := by
  simp only [d2422, h 162 (by decide), agree2259 p q h, agree2201 p q h]
theorem nonnegative2422 (p : Pattern) : 0 ≤ d2422 p :=
  nonnegative_ite (p 162) (nonnegative2259 p) (nonnegative2201 p)
def d2423 (p : Pattern) : Int := if p 161 then d2260 p else d2422 p
theorem agree2423 (p q : Pattern) (h : Agree support p q) : d2423 p = d2423 q := by
  simp only [d2423, h 161 (by decide), agree2260 p q h, agree2422 p q h]
theorem nonnegative2423 (p : Pattern) : 0 ≤ d2423 p :=
  nonnegative_ite (p 161) (nonnegative2260 p) (nonnegative2422 p)
def d2424 (p : Pattern) : Int := if p 224 then d12 p else d191 p
theorem agree2424 (p q : Pattern) (h : Agree support p q) : d2424 p = d2424 q := by
  simp only [d2424, h 224 (by decide), agree12 p q h, agree191 p q h]
theorem nonnegative2424 (p : Pattern) : 0 ≤ d2424 p :=
  nonnegative_ite (p 224) (nonnegative12 p) (nonnegative191 p)
def d2425 (p : Pattern) : Int := if p 204 then d12 p else d2424 p
theorem agree2425 (p q : Pattern) (h : Agree support p q) : d2425 p = d2425 q := by
  simp only [d2425, h 204 (by decide), agree12 p q h, agree2424 p q h]
theorem nonnegative2425 (p : Pattern) : 0 ≤ d2425 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2424 p)
def d2426 (p : Pattern) : Int := if p 182 then d2425 p else d2424 p
theorem agree2426 (p q : Pattern) (h : Agree support p q) : d2426 p = d2426 q := by
  simp only [d2426, h 182 (by decide), agree2425 p q h, agree2424 p q h]
theorem nonnegative2426 (p : Pattern) : 0 ≤ d2426 p :=
  nonnegative_ite (p 182) (nonnegative2425 p) (nonnegative2424 p)
def d2427 (p : Pattern) : Int := if p 163 then d2426 p else d2198 p
theorem agree2427 (p q : Pattern) (h : Agree support p q) : d2427 p = d2427 q := by
  simp only [d2427, h 163 (by decide), agree2426 p q h, agree2198 p q h]
theorem nonnegative2427 (p : Pattern) : 0 ≤ d2427 p :=
  nonnegative_ite (p 163) (nonnegative2426 p) (nonnegative2198 p)
def d2428 (p : Pattern) : Int := if p 162 then d12 p else d2427 p
theorem agree2428 (p q : Pattern) (h : Agree support p q) : d2428 p = d2428 q := by
  simp only [d2428, h 162 (by decide), agree12 p q h, agree2427 p q h]
theorem nonnegative2428 (p : Pattern) : 0 ≤ d2428 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2427 p)
def d2429 (p : Pattern) : Int := if p 161 then d12 p else d2428 p
theorem agree2429 (p q : Pattern) (h : Agree support p q) : d2429 p = d2429 q := by
  simp only [d2429, h 161 (by decide), agree12 p q h, agree2428 p q h]
theorem nonnegative2429 (p : Pattern) : 0 ≤ d2429 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2428 p)
def d2430 (p : Pattern) : Int := if p 160 then d2429 p else d2423 p
theorem agree2430 (p q : Pattern) (h : Agree support p q) : d2430 p = d2430 q := by
  simp only [d2430, h 160 (by decide), agree2429 p q h, agree2423 p q h]
theorem nonnegative2430 (p : Pattern) : 0 ≤ d2430 p :=
  nonnegative_ite (p 160) (nonnegative2429 p) (nonnegative2423 p)
def d2431 (p : Pattern) : Int := if p 163 then d2240 p else d2198 p
theorem agree2431 (p q : Pattern) (h : Agree support p q) : d2431 p = d2431 q := by
  simp only [d2431, h 163 (by decide), agree2240 p q h, agree2198 p q h]
theorem nonnegative2431 (p : Pattern) : 0 ≤ d2431 p :=
  nonnegative_ite (p 163) (nonnegative2240 p) (nonnegative2198 p)
def d2432 (p : Pattern) : Int := if p 162 then d2431 p else d2232 p
theorem agree2432 (p q : Pattern) (h : Agree support p q) : d2432 p = d2432 q := by
  simp only [d2432, h 162 (by decide), agree2431 p q h, agree2232 p q h]
theorem nonnegative2432 (p : Pattern) : 0 ≤ d2432 p :=
  nonnegative_ite (p 162) (nonnegative2431 p) (nonnegative2232 p)
def d2433 (p : Pattern) : Int := if p 161 then d2267 p else d2432 p
theorem agree2433 (p q : Pattern) (h : Agree support p q) : d2433 p = d2433 q := by
  simp only [d2433, h 161 (by decide), agree2267 p q h, agree2432 p q h]
theorem nonnegative2433 (p : Pattern) : 0 ≤ d2433 p :=
  nonnegative_ite (p 161) (nonnegative2267 p) (nonnegative2432 p)
def d2434 (p : Pattern) : Int := if p 163 then d12 p else d2426 p
theorem agree2434 (p q : Pattern) (h : Agree support p q) : d2434 p = d2434 q := by
  simp only [d2434, h 163 (by decide), agree12 p q h, agree2426 p q h]
theorem nonnegative2434 (p : Pattern) : 0 ≤ d2434 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2426 p)
def d2435 (p : Pattern) : Int := if p 162 then d12 p else d2434 p
theorem agree2435 (p q : Pattern) (h : Agree support p q) : d2435 p = d2435 q := by
  simp only [d2435, h 162 (by decide), agree12 p q h, agree2434 p q h]
theorem nonnegative2435 (p : Pattern) : 0 ≤ d2435 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2434 p)
def d2436 (p : Pattern) : Int := if p 161 then d12 p else d2435 p
theorem agree2436 (p q : Pattern) (h : Agree support p q) : d2436 p = d2436 q := by
  simp only [d2436, h 161 (by decide), agree12 p q h, agree2435 p q h]
theorem nonnegative2436 (p : Pattern) : 0 ≤ d2436 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2435 p)
def d2437 (p : Pattern) : Int := if p 160 then d2436 p else d2433 p
theorem agree2437 (p q : Pattern) (h : Agree support p q) : d2437 p = d2437 q := by
  simp only [d2437, h 160 (by decide), agree2436 p q h, agree2433 p q h]
theorem nonnegative2437 (p : Pattern) : 0 ≤ d2437 p :=
  nonnegative_ite (p 160) (nonnegative2436 p) (nonnegative2433 p)
def d2438 (p : Pattern) : Int := if p 141 then d2437 p else d2430 p
theorem agree2438 (p q : Pattern) (h : Agree support p q) : d2438 p = d2438 q := by
  simp only [d2438, h 141 (by decide), agree2437 p q h, agree2430 p q h]
theorem nonnegative2438 (p : Pattern) : 0 ≤ d2438 p :=
  nonnegative_ite (p 141) (nonnegative2437 p) (nonnegative2430 p)
def d2439 (p : Pattern) : Int := if p 138 then d2438 p else d2421 p
theorem agree2439 (p q : Pattern) (h : Agree support p q) : d2439 p = d2439 q := by
  simp only [d2439, h 138 (by decide), agree2438 p q h, agree2421 p q h]
theorem nonnegative2439 (p : Pattern) : 0 ≤ d2439 p :=
  nonnegative_ite (p 138) (nonnegative2438 p) (nonnegative2421 p)
def d2440 (p : Pattern) : Int := if p 138 then d12 p else d2438 p
theorem agree2440 (p q : Pattern) (h : Agree support p q) : d2440 p = d2440 q := by
  simp only [d2440, h 138 (by decide), agree12 p q h, agree2438 p q h]
theorem nonnegative2440 (p : Pattern) : 0 ≤ d2440 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative2438 p)
def d2441 (p : Pattern) : Int := if p 116 then d2440 p else d2439 p
theorem agree2441 (p q : Pattern) (h : Agree support p q) : d2441 p = d2441 q := by
  simp only [d2441, h 116 (by decide), agree2440 p q h, agree2439 p q h]
theorem nonnegative2441 (p : Pattern) : 0 ≤ d2441 p :=
  nonnegative_ite (p 116) (nonnegative2440 p) (nonnegative2439 p)
def d2442 (p : Pattern) : Int := if p 115 then d2441 p else d2311 p
theorem agree2442 (p q : Pattern) (h : Agree support p q) : d2442 p = d2442 q := by
  simp only [d2442, h 115 (by decide), agree2441 p q h, agree2311 p q h]
theorem nonnegative2442 (p : Pattern) : 0 ≤ d2442 p :=
  nonnegative_ite (p 115) (nonnegative2441 p) (nonnegative2311 p)
def d2443 (p : Pattern) : Int := if p 71 then d2442 p else d2296 p
theorem agree2443 (p q : Pattern) (h : Agree support p q) : d2443 p = d2443 q := by
  simp only [d2443, h 71 (by decide), agree2442 p q h, agree2296 p q h]
theorem nonnegative2443 (p : Pattern) : 0 ≤ d2443 p :=
  nonnegative_ite (p 71) (nonnegative2442 p) (nonnegative2296 p)
def d2444 (p : Pattern) : Int := if p 163 then d12 p else d2330 p
theorem agree2444 (p q : Pattern) (h : Agree support p q) : d2444 p = d2444 q := by
  simp only [d2444, h 163 (by decide), agree12 p q h, agree2330 p q h]
theorem nonnegative2444 (p : Pattern) : 0 ≤ d2444 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2330 p)
def d2445 (p : Pattern) : Int := if p 162 then d2444 p else d2355 p
theorem agree2445 (p q : Pattern) (h : Agree support p q) : d2445 p = d2445 q := by
  simp only [d2445, h 162 (by decide), agree2444 p q h, agree2355 p q h]
theorem nonnegative2445 (p : Pattern) : 0 ≤ d2445 p :=
  nonnegative_ite (p 162) (nonnegative2444 p) (nonnegative2355 p)
def d2446 (p : Pattern) : Int := if p 162 then d12 p else d2444 p
theorem agree2446 (p q : Pattern) (h : Agree support p q) : d2446 p = d2446 q := by
  simp only [d2446, h 162 (by decide), agree12 p q h, agree2444 p q h]
theorem nonnegative2446 (p : Pattern) : 0 ≤ d2446 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2444 p)
def d2447 (p : Pattern) : Int := if p 161 then d2446 p else d2445 p
theorem agree2447 (p q : Pattern) (h : Agree support p q) : d2447 p = d2447 q := by
  simp only [d2447, h 161 (by decide), agree2446 p q h, agree2445 p q h]
theorem nonnegative2447 (p : Pattern) : 0 ≤ d2447 p :=
  nonnegative_ite (p 161) (nonnegative2446 p) (nonnegative2445 p)
def d2448 (p : Pattern) : Int := if p 163 then d12 p else d2344 p
theorem agree2448 (p q : Pattern) (h : Agree support p q) : d2448 p = d2448 q := by
  simp only [d2448, h 163 (by decide), agree12 p q h, agree2344 p q h]
theorem nonnegative2448 (p : Pattern) : 0 ≤ d2448 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2344 p)
def d2449 (p : Pattern) : Int := if p 162 then d2448 p else d2362 p
theorem agree2449 (p q : Pattern) (h : Agree support p q) : d2449 p = d2449 q := by
  simp only [d2449, h 162 (by decide), agree2448 p q h, agree2362 p q h]
theorem nonnegative2449 (p : Pattern) : 0 ≤ d2449 p :=
  nonnegative_ite (p 162) (nonnegative2448 p) (nonnegative2362 p)
def d2450 (p : Pattern) : Int := if p 162 then d12 p else d2448 p
theorem agree2450 (p q : Pattern) (h : Agree support p q) : d2450 p = d2450 q := by
  simp only [d2450, h 162 (by decide), agree12 p q h, agree2448 p q h]
theorem nonnegative2450 (p : Pattern) : 0 ≤ d2450 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2448 p)
def d2451 (p : Pattern) : Int := if p 161 then d2450 p else d2449 p
theorem agree2451 (p q : Pattern) (h : Agree support p q) : d2451 p = d2451 q := by
  simp only [d2451, h 161 (by decide), agree2450 p q h, agree2449 p q h]
theorem nonnegative2451 (p : Pattern) : 0 ≤ d2451 p :=
  nonnegative_ite (p 161) (nonnegative2450 p) (nonnegative2449 p)
def d2452 (p : Pattern) : Int := if p 160 then d2451 p else d2447 p
theorem agree2452 (p q : Pattern) (h : Agree support p q) : d2452 p = d2452 q := by
  simp only [d2452, h 160 (by decide), agree2451 p q h, agree2447 p q h]
theorem nonnegative2452 (p : Pattern) : 0 ≤ d2452 p :=
  nonnegative_ite (p 160) (nonnegative2451 p) (nonnegative2447 p)
def d2453 (p : Pattern) : Int := if p 141 then d2452 p else d2350 p
theorem agree2453 (p q : Pattern) (h : Agree support p q) : d2453 p = d2453 q := by
  simp only [d2453, h 141 (by decide), agree2452 p q h, agree2350 p q h]
theorem nonnegative2453 (p : Pattern) : 0 ≤ d2453 p :=
  nonnegative_ite (p 141) (nonnegative2452 p) (nonnegative2350 p)
def d2454 (p : Pattern) : Int := if p 162 then d2444 p else d2377 p
theorem agree2454 (p q : Pattern) (h : Agree support p q) : d2454 p = d2454 q := by
  simp only [d2454, h 162 (by decide), agree2444 p q h, agree2377 p q h]
theorem nonnegative2454 (p : Pattern) : 0 ≤ d2454 p :=
  nonnegative_ite (p 162) (nonnegative2444 p) (nonnegative2377 p)
def d2455 (p : Pattern) : Int := if p 161 then d2446 p else d2454 p
theorem agree2455 (p q : Pattern) (h : Agree support p q) : d2455 p = d2455 q := by
  simp only [d2455, h 161 (by decide), agree2446 p q h, agree2454 p q h]
theorem nonnegative2455 (p : Pattern) : 0 ≤ d2455 p :=
  nonnegative_ite (p 161) (nonnegative2446 p) (nonnegative2454 p)
def d2456 (p : Pattern) : Int := if p 160 then d2382 p else d2455 p
theorem agree2456 (p q : Pattern) (h : Agree support p q) : d2456 p = d2456 q := by
  simp only [d2456, h 160 (by decide), agree2382 p q h, agree2455 p q h]
theorem nonnegative2456 (p : Pattern) : 0 ≤ d2456 p :=
  nonnegative_ite (p 160) (nonnegative2382 p) (nonnegative2455 p)
def d2457 (p : Pattern) : Int := if p 141 then d2456 p else d2376 p
theorem agree2457 (p q : Pattern) (h : Agree support p q) : d2457 p = d2457 q := by
  simp only [d2457, h 141 (by decide), agree2456 p q h, agree2376 p q h]
theorem nonnegative2457 (p : Pattern) : 0 ≤ d2457 p :=
  nonnegative_ite (p 141) (nonnegative2456 p) (nonnegative2376 p)
def d2458 (p : Pattern) : Int := if p 138 then d2457 p else d2453 p
theorem agree2458 (p q : Pattern) (h : Agree support p q) : d2458 p = d2458 q := by
  simp only [d2458, h 138 (by decide), agree2457 p q h, agree2453 p q h]
theorem nonnegative2458 (p : Pattern) : 0 ≤ d2458 p :=
  nonnegative_ite (p 138) (nonnegative2457 p) (nonnegative2453 p)
def d2459 (p : Pattern) : Int := if p 138 then d2389 p else d2457 p
theorem agree2459 (p q : Pattern) (h : Agree support p q) : d2459 p = d2459 q := by
  simp only [d2459, h 138 (by decide), agree2389 p q h, agree2457 p q h]
theorem nonnegative2459 (p : Pattern) : 0 ≤ d2459 p :=
  nonnegative_ite (p 138) (nonnegative2389 p) (nonnegative2457 p)
def d2460 (p : Pattern) : Int := if p 116 then d2459 p else d2458 p
theorem agree2460 (p q : Pattern) (h : Agree support p q) : d2460 p = d2460 q := by
  simp only [d2460, h 116 (by decide), agree2459 p q h, agree2458 p q h]
theorem nonnegative2460 (p : Pattern) : 0 ≤ d2460 p :=
  nonnegative_ite (p 116) (nonnegative2459 p) (nonnegative2458 p)
def d2461 (p : Pattern) : Int := if p 182 then d2340 p else d2336 p
theorem agree2461 (p q : Pattern) (h : Agree support p q) : d2461 p = d2461 q := by
  simp only [d2461, h 182 (by decide), agree2340 p q h, agree2336 p q h]
theorem nonnegative2461 (p : Pattern) : 0 ≤ d2461 p :=
  nonnegative_ite (p 182) (nonnegative2340 p) (nonnegative2336 p)
def d2462 (p : Pattern) : Int := if p 163 then d2461 p else d2354 p
theorem agree2462 (p q : Pattern) (h : Agree support p q) : d2462 p = d2462 q := by
  simp only [d2462, h 163 (by decide), agree2461 p q h, agree2354 p q h]
theorem nonnegative2462 (p : Pattern) : 0 ≤ d2462 p :=
  nonnegative_ite (p 163) (nonnegative2461 p) (nonnegative2354 p)
def d2463 (p : Pattern) : Int := if p 162 then d2448 p else d2462 p
theorem agree2463 (p q : Pattern) (h : Agree support p q) : d2463 p = d2463 q := by
  simp only [d2463, h 162 (by decide), agree2448 p q h, agree2462 p q h]
theorem nonnegative2463 (p : Pattern) : 0 ≤ d2463 p :=
  nonnegative_ite (p 162) (nonnegative2448 p) (nonnegative2462 p)
def d2464 (p : Pattern) : Int := if p 182 then d12 p else d2339 p
theorem agree2464 (p q : Pattern) (h : Agree support p q) : d2464 p = d2464 q := by
  simp only [d2464, h 182 (by decide), agree12 p q h, agree2339 p q h]
theorem nonnegative2464 (p : Pattern) : 0 ≤ d2464 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2339 p)
def d2465 (p : Pattern) : Int := if p 163 then d12 p else d2464 p
theorem agree2465 (p q : Pattern) (h : Agree support p q) : d2465 p = d2465 q := by
  simp only [d2465, h 163 (by decide), agree12 p q h, agree2464 p q h]
theorem nonnegative2465 (p : Pattern) : 0 ≤ d2465 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2464 p)
def d2466 (p : Pattern) : Int := if p 162 then d12 p else d2465 p
theorem agree2466 (p q : Pattern) (h : Agree support p q) : d2466 p = d2466 q := by
  simp only [d2466, h 162 (by decide), agree12 p q h, agree2465 p q h]
theorem nonnegative2466 (p : Pattern) : 0 ≤ d2466 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2465 p)
def d2467 (p : Pattern) : Int := if p 161 then d2466 p else d2463 p
theorem agree2467 (p q : Pattern) (h : Agree support p q) : d2467 p = d2467 q := by
  simp only [d2467, h 161 (by decide), agree2466 p q h, agree2463 p q h]
theorem nonnegative2467 (p : Pattern) : 0 ≤ d2467 p :=
  nonnegative_ite (p 161) (nonnegative2466 p) (nonnegative2463 p)
def d2468 (p : Pattern) : Int := if p 160 then d2467 p else d2394 p
theorem agree2468 (p q : Pattern) (h : Agree support p q) : d2468 p = d2468 q := by
  simp only [d2468, h 160 (by decide), agree2467 p q h, agree2394 p q h]
theorem nonnegative2468 (p : Pattern) : 0 ≤ d2468 p :=
  nonnegative_ite (p 160) (nonnegative2467 p) (nonnegative2394 p)
def d2469 (p : Pattern) : Int := if p 182 then d2340 p else d2328 p
theorem agree2469 (p q : Pattern) (h : Agree support p q) : d2469 p = d2469 q := by
  simp only [d2469, h 182 (by decide), agree2340 p q h, agree2328 p q h]
theorem nonnegative2469 (p : Pattern) : 0 ≤ d2469 p :=
  nonnegative_ite (p 182) (nonnegative2340 p) (nonnegative2328 p)
def d2470 (p : Pattern) : Int := if p 163 then d2344 p else d2469 p
theorem agree2470 (p q : Pattern) (h : Agree support p q) : d2470 p = d2470 q := by
  simp only [d2470, h 163 (by decide), agree2344 p q h, agree2469 p q h]
theorem nonnegative2470 (p : Pattern) : 0 ≤ d2470 p :=
  nonnegative_ite (p 163) (nonnegative2344 p) (nonnegative2469 p)
def d2471 (p : Pattern) : Int := if p 162 then d2465 p else d2470 p
theorem agree2471 (p q : Pattern) (h : Agree support p q) : d2471 p = d2471 q := by
  simp only [d2471, h 162 (by decide), agree2465 p q h, agree2470 p q h]
theorem nonnegative2471 (p : Pattern) : 0 ≤ d2471 p :=
  nonnegative_ite (p 162) (nonnegative2465 p) (nonnegative2470 p)
def d2472 (p : Pattern) : Int := if p 162 then d12 p else d2225 p
theorem agree2472 (p q : Pattern) (h : Agree support p q) : d2472 p = d2472 q := by
  simp only [d2472, h 162 (by decide), agree12 p q h, agree2225 p q h]
theorem nonnegative2472 (p : Pattern) : 0 ≤ d2472 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2225 p)
def d2473 (p : Pattern) : Int := if p 161 then d2472 p else d2471 p
theorem agree2473 (p q : Pattern) (h : Agree support p q) : d2473 p = d2473 q := by
  simp only [d2473, h 161 (by decide), agree2472 p q h, agree2471 p q h]
theorem nonnegative2473 (p : Pattern) : 0 ≤ d2473 p :=
  nonnegative_ite (p 161) (nonnegative2472 p) (nonnegative2471 p)
def d2474 (p : Pattern) : Int := if p 160 then d2473 p else d2455 p
theorem agree2474 (p q : Pattern) (h : Agree support p q) : d2474 p = d2474 q := by
  simp only [d2474, h 160 (by decide), agree2473 p q h, agree2455 p q h]
theorem nonnegative2474 (p : Pattern) : 0 ≤ d2474 p :=
  nonnegative_ite (p 160) (nonnegative2473 p) (nonnegative2455 p)
def d2475 (p : Pattern) : Int := if p 141 then d2474 p else d2468 p
theorem agree2475 (p q : Pattern) (h : Agree support p q) : d2475 p = d2475 q := by
  simp only [d2475, h 141 (by decide), agree2474 p q h, agree2468 p q h]
theorem nonnegative2475 (p : Pattern) : 0 ≤ d2475 p :=
  nonnegative_ite (p 141) (nonnegative2474 p) (nonnegative2468 p)
def d2476 (p : Pattern) : Int := if p 163 then d2240 p else d2354 p
theorem agree2476 (p q : Pattern) (h : Agree support p q) : d2476 p = d2476 q := by
  simp only [d2476, h 163 (by decide), agree2240 p q h, agree2354 p q h]
theorem nonnegative2476 (p : Pattern) : 0 ≤ d2476 p :=
  nonnegative_ite (p 163) (nonnegative2240 p) (nonnegative2354 p)
def d2477 (p : Pattern) : Int := if p 162 then d2476 p else d2327 p
theorem agree2477 (p q : Pattern) (h : Agree support p q) : d2477 p = d2477 q := by
  simp only [d2477, h 162 (by decide), agree2476 p q h, agree2327 p q h]
theorem nonnegative2477 (p : Pattern) : 0 ≤ d2477 p :=
  nonnegative_ite (p 162) (nonnegative2476 p) (nonnegative2327 p)
def d2478 (p : Pattern) : Int := if p 161 then d2359 p else d2477 p
theorem agree2478 (p q : Pattern) (h : Agree support p q) : d2478 p = d2478 q := by
  simp only [d2478, h 161 (by decide), agree2359 p q h, agree2477 p q h]
theorem nonnegative2478 (p : Pattern) : 0 ≤ d2478 p :=
  nonnegative_ite (p 161) (nonnegative2359 p) (nonnegative2477 p)
def d2479 (p : Pattern) : Int := if p 160 then d2382 p else d2478 p
theorem agree2479 (p q : Pattern) (h : Agree support p q) : d2479 p = d2479 q := by
  simp only [d2479, h 160 (by decide), agree2382 p q h, agree2478 p q h]
theorem nonnegative2479 (p : Pattern) : 0 ≤ d2479 p :=
  nonnegative_ite (p 160) (nonnegative2382 p) (nonnegative2478 p)
def d2480 (p : Pattern) : Int := if p 162 then d2444 p else d2354 p
theorem agree2480 (p q : Pattern) (h : Agree support p q) : d2480 p = d2480 q := by
  simp only [d2480, h 162 (by decide), agree2444 p q h, agree2354 p q h]
theorem nonnegative2480 (p : Pattern) : 0 ≤ d2480 p :=
  nonnegative_ite (p 162) (nonnegative2444 p) (nonnegative2354 p)
def d2481 (p : Pattern) : Int := if p 161 then d2381 p else d2480 p
theorem agree2481 (p q : Pattern) (h : Agree support p q) : d2481 p = d2481 q := by
  simp only [d2481, h 161 (by decide), agree2381 p q h, agree2480 p q h]
theorem nonnegative2481 (p : Pattern) : 0 ≤ d2481 p :=
  nonnegative_ite (p 161) (nonnegative2381 p) (nonnegative2480 p)
def d2482 (p : Pattern) : Int := if p 162 then d12 p else d2206 p
theorem agree2482 (p q : Pattern) (h : Agree support p q) : d2482 p = d2482 q := by
  simp only [d2482, h 162 (by decide), agree12 p q h, agree2206 p q h]
theorem nonnegative2482 (p : Pattern) : 0 ≤ d2482 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2206 p)
def d2483 (p : Pattern) : Int := if p 161 then d12 p else d2482 p
theorem agree2483 (p q : Pattern) (h : Agree support p q) : d2483 p = d2483 q := by
  simp only [d2483, h 161 (by decide), agree12 p q h, agree2482 p q h]
theorem nonnegative2483 (p : Pattern) : 0 ≤ d2483 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2482 p)
def d2484 (p : Pattern) : Int := if p 160 then d2483 p else d2481 p
theorem agree2484 (p q : Pattern) (h : Agree support p q) : d2484 p = d2484 q := by
  simp only [d2484, h 160 (by decide), agree2483 p q h, agree2481 p q h]
theorem nonnegative2484 (p : Pattern) : 0 ≤ d2484 p :=
  nonnegative_ite (p 160) (nonnegative2483 p) (nonnegative2481 p)
def d2485 (p : Pattern) : Int := if p 141 then d2484 p else d2479 p
theorem agree2485 (p q : Pattern) (h : Agree support p q) : d2485 p = d2485 q := by
  simp only [d2485, h 141 (by decide), agree2484 p q h, agree2479 p q h]
theorem nonnegative2485 (p : Pattern) : 0 ≤ d2485 p :=
  nonnegative_ite (p 141) (nonnegative2484 p) (nonnegative2479 p)
def d2486 (p : Pattern) : Int := if p 138 then d2485 p else d2475 p
theorem agree2486 (p q : Pattern) (h : Agree support p q) : d2486 p = d2486 q := by
  simp only [d2486, h 138 (by decide), agree2485 p q h, agree2475 p q h]
theorem nonnegative2486 (p : Pattern) : 0 ≤ d2486 p :=
  nonnegative_ite (p 138) (nonnegative2485 p) (nonnegative2475 p)
def d2487 (p : Pattern) : Int := if p 163 then d2205 p else d2354 p
theorem agree2487 (p q : Pattern) (h : Agree support p q) : d2487 p = d2487 q := by
  simp only [d2487, h 163 (by decide), agree2205 p q h, agree2354 p q h]
theorem nonnegative2487 (p : Pattern) : 0 ≤ d2487 p :=
  nonnegative_ite (p 163) (nonnegative2205 p) (nonnegative2354 p)
def d2488 (p : Pattern) : Int := if p 162 then d2487 p else d2327 p
theorem agree2488 (p q : Pattern) (h : Agree support p q) : d2488 p = d2488 q := by
  simp only [d2488, h 162 (by decide), agree2487 p q h, agree2327 p q h]
theorem nonnegative2488 (p : Pattern) : 0 ≤ d2488 p :=
  nonnegative_ite (p 162) (nonnegative2487 p) (nonnegative2327 p)
def d2489 (p : Pattern) : Int := if p 163 then d2205 p else d2330 p
theorem agree2489 (p q : Pattern) (h : Agree support p q) : d2489 p = d2489 q := by
  simp only [d2489, h 163 (by decide), agree2205 p q h, agree2330 p q h]
theorem nonnegative2489 (p : Pattern) : 0 ≤ d2489 p :=
  nonnegative_ite (p 163) (nonnegative2205 p) (nonnegative2330 p)
def d2490 (p : Pattern) : Int := if p 162 then d12 p else d2489 p
theorem agree2490 (p q : Pattern) (h : Agree support p q) : d2490 p = d2490 q := by
  simp only [d2490, h 162 (by decide), agree12 p q h, agree2489 p q h]
theorem nonnegative2490 (p : Pattern) : 0 ≤ d2490 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2489 p)
def d2491 (p : Pattern) : Int := if p 161 then d2490 p else d2488 p
theorem agree2491 (p q : Pattern) (h : Agree support p q) : d2491 p = d2491 q := by
  simp only [d2491, h 161 (by decide), agree2490 p q h, agree2488 p q h]
theorem nonnegative2491 (p : Pattern) : 0 ≤ d2491 p :=
  nonnegative_ite (p 161) (nonnegative2490 p) (nonnegative2488 p)
def d2492 (p : Pattern) : Int := if p 163 then d2240 p else d2372 p
theorem agree2492 (p q : Pattern) (h : Agree support p q) : d2492 p = d2492 q := by
  simp only [d2492, h 163 (by decide), agree2240 p q h, agree2372 p q h]
theorem nonnegative2492 (p : Pattern) : 0 ≤ d2492 p :=
  nonnegative_ite (p 163) (nonnegative2240 p) (nonnegative2372 p)
def d2493 (p : Pattern) : Int := if p 162 then d12 p else d2492 p
theorem agree2493 (p q : Pattern) (h : Agree support p q) : d2493 p = d2493 q := by
  simp only [d2493, h 162 (by decide), agree12 p q h, agree2492 p q h]
theorem nonnegative2493 (p : Pattern) : 0 ≤ d2493 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2492 p)
def d2494 (p : Pattern) : Int := if p 161 then d12 p else d2493 p
theorem agree2494 (p q : Pattern) (h : Agree support p q) : d2494 p = d2494 q := by
  simp only [d2494, h 161 (by decide), agree12 p q h, agree2493 p q h]
theorem nonnegative2494 (p : Pattern) : 0 ≤ d2494 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2493 p)
def d2495 (p : Pattern) : Int := if p 160 then d2494 p else d2491 p
theorem agree2495 (p q : Pattern) (h : Agree support p q) : d2495 p = d2495 q := by
  simp only [d2495, h 160 (by decide), agree2494 p q h, agree2491 p q h]
theorem nonnegative2495 (p : Pattern) : 0 ≤ d2495 p :=
  nonnegative_ite (p 160) (nonnegative2494 p) (nonnegative2491 p)
def d2496 (p : Pattern) : Int := if p 141 then d2484 p else d2495 p
theorem agree2496 (p q : Pattern) (h : Agree support p q) : d2496 p = d2496 q := by
  simp only [d2496, h 141 (by decide), agree2484 p q h, agree2495 p q h]
theorem nonnegative2496 (p : Pattern) : 0 ≤ d2496 p :=
  nonnegative_ite (p 141) (nonnegative2484 p) (nonnegative2495 p)
def d2497 (p : Pattern) : Int := if p 138 then d12 p else d2496 p
theorem agree2497 (p q : Pattern) (h : Agree support p q) : d2497 p = d2497 q := by
  simp only [d2497, h 138 (by decide), agree12 p q h, agree2496 p q h]
theorem nonnegative2497 (p : Pattern) : 0 ≤ d2497 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative2496 p)
def d2498 (p : Pattern) : Int := if p 116 then d2497 p else d2486 p
theorem agree2498 (p q : Pattern) (h : Agree support p q) : d2498 p = d2498 q := by
  simp only [d2498, h 116 (by decide), agree2497 p q h, agree2486 p q h]
theorem nonnegative2498 (p : Pattern) : 0 ≤ d2498 p :=
  nonnegative_ite (p 116) (nonnegative2497 p) (nonnegative2486 p)
def d2499 (p : Pattern) : Int := if p 115 then d2498 p else d2460 p
theorem agree2499 (p q : Pattern) (h : Agree support p q) : d2499 p = d2499 q := by
  simp only [d2499, h 115 (by decide), agree2498 p q h, agree2460 p q h]
theorem nonnegative2499 (p : Pattern) : 0 ≤ d2499 p :=
  nonnegative_ite (p 115) (nonnegative2498 p) (nonnegative2460 p)
def d2500 (p : Pattern) : Int := if p 71 then d2499 p else d2296 p
theorem agree2500 (p q : Pattern) (h : Agree support p q) : d2500 p = d2500 q := by
  simp only [d2500, h 71 (by decide), agree2499 p q h, agree2296 p q h]
theorem nonnegative2500 (p : Pattern) : 0 ≤ d2500 p :=
  nonnegative_ite (p 71) (nonnegative2499 p) (nonnegative2296 p)
def d2501 (p : Pattern) : Int := if p 49 then d2500 p else d2443 p
theorem agree2501 (p q : Pattern) (h : Agree support p q) : d2501 p = d2501 q := by
  simp only [d2501, h 49 (by decide), agree2500 p q h, agree2443 p q h]
theorem nonnegative2501 (p : Pattern) : 0 ≤ d2501 p :=
  nonnegative_ite (p 49) (nonnegative2500 p) (nonnegative2443 p)
def d2502 (p : Pattern) : Int := if p 48 then d2501 p else d2403 p
theorem agree2502 (p q : Pattern) (h : Agree support p q) : d2502 p = d2502 q := by
  simp only [d2502, h 48 (by decide), agree2501 p q h, agree2403 p q h]
theorem nonnegative2502 (p : Pattern) : 0 ≤ d2502 p :=
  nonnegative_ite (p 48) (nonnegative2501 p) (nonnegative2403 p)
def d2503 (p : Pattern) : Int := if p 225 then d315 p else d14 p
theorem agree2503 (p q : Pattern) (h : Agree support p q) : d2503 p = d2503 q := by
  simp only [d2503, h 225 (by decide), agree315 p q h, agree14 p q h]
theorem nonnegative2503 (p : Pattern) : 0 ≤ d2503 p :=
  nonnegative_ite (p 225) (nonnegative315 p) (nonnegative14 p)
def d2504 (p : Pattern) : Int := if p 225 then d12 p else d14 p
theorem agree2504 (p q : Pattern) (h : Agree support p q) : d2504 p = d2504 q := by
  simp only [d2504, h 225 (by decide), agree12 p q h, agree14 p q h]
theorem nonnegative2504 (p : Pattern) : 0 ≤ d2504 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative14 p)
def d2505 (p : Pattern) : Int := if p 224 then d2504 p else d2503 p
theorem agree2505 (p q : Pattern) (h : Agree support p q) : d2505 p = d2505 q := by
  simp only [d2505, h 224 (by decide), agree2504 p q h, agree2503 p q h]
theorem nonnegative2505 (p : Pattern) : 0 ≤ d2505 p :=
  nonnegative_ite (p 224) (nonnegative2504 p) (nonnegative2503 p)
def d2506 (p : Pattern) : Int := if p 225 then d12 p else d1770 p
theorem agree2506 (p q : Pattern) (h : Agree support p q) : d2506 p = d2506 q := by
  simp only [d2506, h 225 (by decide), agree12 p q h, agree1770 p q h]
theorem nonnegative2506 (p : Pattern) : 0 ≤ d2506 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative1770 p)
def d2507 (p : Pattern) : Int := if p 224 then d2506 p else d2504 p
theorem agree2507 (p q : Pattern) (h : Agree support p q) : d2507 p = d2507 q := by
  simp only [d2507, h 224 (by decide), agree2506 p q h, agree2504 p q h]
theorem nonnegative2507 (p : Pattern) : 0 ≤ d2507 p :=
  nonnegative_ite (p 224) (nonnegative2506 p) (nonnegative2504 p)
def d2508 (p : Pattern) : Int := if p 204 then d2507 p else d2505 p
theorem agree2508 (p q : Pattern) (h : Agree support p q) : d2508 p = d2508 q := by
  simp only [d2508, h 204 (by decide), agree2507 p q h, agree2505 p q h]
theorem nonnegative2508 (p : Pattern) : 0 ≤ d2508 p :=
  nonnegative_ite (p 204) (nonnegative2507 p) (nonnegative2505 p)
def d2509 (p : Pattern) : Int := if p 225 then d12 p else d1684 p
theorem agree2509 (p q : Pattern) (h : Agree support p q) : d2509 p = d2509 q := by
  simp only [d2509, h 225 (by decide), agree12 p q h, agree1684 p q h]
theorem nonnegative2509 (p : Pattern) : 0 ≤ d2509 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative1684 p)
def d2510 (p : Pattern) : Int := if p 224 then d2509 p else d2504 p
theorem agree2510 (p q : Pattern) (h : Agree support p q) : d2510 p = d2510 q := by
  simp only [d2510, h 224 (by decide), agree2509 p q h, agree2504 p q h]
theorem nonnegative2510 (p : Pattern) : 0 ≤ d2510 p :=
  nonnegative_ite (p 224) (nonnegative2509 p) (nonnegative2504 p)
def d2511 (p : Pattern) : Int := if p 204 then d12 p else d2510 p
theorem agree2511 (p q : Pattern) (h : Agree support p q) : d2511 p = d2511 q := by
  simp only [d2511, h 204 (by decide), agree12 p q h, agree2510 p q h]
theorem nonnegative2511 (p : Pattern) : 0 ≤ d2511 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2510 p)
def d2512 (p : Pattern) : Int := if p 182 then d2511 p else d2508 p
theorem agree2512 (p q : Pattern) (h : Agree support p q) : d2512 p = d2512 q := by
  simp only [d2512, h 182 (by decide), agree2511 p q h, agree2508 p q h]
theorem nonnegative2512 (p : Pattern) : 0 ≤ d2512 p :=
  nonnegative_ite (p 182) (nonnegative2511 p) (nonnegative2508 p)
def d2513 (p : Pattern) : Int := if p 225 then d327 p else d14 p
theorem agree2513 (p q : Pattern) (h : Agree support p q) : d2513 p = d2513 q := by
  simp only [d2513, h 225 (by decide), agree327 p q h, agree14 p q h]
theorem nonnegative2513 (p : Pattern) : 0 ≤ d2513 p :=
  nonnegative_ite (p 225) (nonnegative327 p) (nonnegative14 p)
def d2514 (p : Pattern) : Int := if p 224 then d2504 p else d2513 p
theorem agree2514 (p q : Pattern) (h : Agree support p q) : d2514 p = d2514 q := by
  simp only [d2514, h 224 (by decide), agree2504 p q h, agree2513 p q h]
theorem nonnegative2514 (p : Pattern) : 0 ≤ d2514 p :=
  nonnegative_ite (p 224) (nonnegative2504 p) (nonnegative2513 p)
def d2515 (p : Pattern) : Int := if p 204 then d2507 p else d2514 p
theorem agree2515 (p q : Pattern) (h : Agree support p q) : d2515 p = d2515 q := by
  simp only [d2515, h 204 (by decide), agree2507 p q h, agree2514 p q h]
theorem nonnegative2515 (p : Pattern) : 0 ≤ d2515 p :=
  nonnegative_ite (p 204) (nonnegative2507 p) (nonnegative2514 p)
def d2516 (p : Pattern) : Int := if p 182 then d2511 p else d2515 p
theorem agree2516 (p q : Pattern) (h : Agree support p q) : d2516 p = d2516 q := by
  simp only [d2516, h 182 (by decide), agree2511 p q h, agree2515 p q h]
theorem nonnegative2516 (p : Pattern) : 0 ≤ d2516 p :=
  nonnegative_ite (p 182) (nonnegative2511 p) (nonnegative2515 p)
def d2517 (p : Pattern) : Int := if p 163 then d2516 p else d2512 p
theorem agree2517 (p q : Pattern) (h : Agree support p q) : d2517 p = d2517 q := by
  simp only [d2517, h 163 (by decide), agree2516 p q h, agree2512 p q h]
theorem nonnegative2517 (p : Pattern) : 0 ≤ d2517 p :=
  nonnegative_ite (p 163) (nonnegative2516 p) (nonnegative2512 p)
def d2518 (p : Pattern) : Int := if p 204 then d2507 p else d2504 p
theorem agree2518 (p q : Pattern) (h : Agree support p q) : d2518 p = d2518 q := by
  simp only [d2518, h 204 (by decide), agree2507 p q h, agree2504 p q h]
theorem nonnegative2518 (p : Pattern) : 0 ≤ d2518 p :=
  nonnegative_ite (p 204) (nonnegative2507 p) (nonnegative2504 p)
def d2519 (p : Pattern) : Int := if p 182 then d2511 p else d2518 p
theorem agree2519 (p q : Pattern) (h : Agree support p q) : d2519 p = d2519 q := by
  simp only [d2519, h 182 (by decide), agree2511 p q h, agree2518 p q h]
theorem nonnegative2519 (p : Pattern) : 0 ≤ d2519 p :=
  nonnegative_ite (p 182) (nonnegative2511 p) (nonnegative2518 p)
end NetHack.Sokoban22Refined85
