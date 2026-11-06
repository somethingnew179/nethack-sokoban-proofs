/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2380 (p : Pattern) (guard : d0 p = 1) : d139 p ≤ (0 : Int) + d122 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2381 (p : Pattern) (guard : d4148 p = 1) : d140 p ≤ (0 : Int) + d122 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2379 p hg
    simpa only [d4148, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2380 p hg
    simpa only [d4148, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2382 (p : Pattern) (guard : d1 p = 1) : d125 p ≤ (0 : Int) + d125 p := by
  omega
theorem compare2383 (p : Pattern) (guard : d0 p = 1) : d70 p ≤ (0 : Int) + d125 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2384 (p : Pattern) (guard : d4148 p = 1) : d141 p ≤ (0 : Int) + d125 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2382 p hg
    simpa only [d4148, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2383 p hg
    simpa only [d4148, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2385 (p : Pattern) (guard : d4148 p = 1) : d142 p ≤ (0 : Int) + d4170 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d142, d4170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2381 p hg
    simpa only [d142, d4170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d142, d4170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2384 p hg
    simpa only [d142, d4170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2386 (p : Pattern) (guard : d0 p = 1) : d72 p ≤ (0 : Int) + d125 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2387 (p : Pattern) (guard : d4148 p = 1) : d143 p ≤ (0 : Int) + d125 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2382 p hg
    simpa only [d4148, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2386 p hg
    simpa only [d4148, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2388 (p : Pattern) (guard : d4148 p = 1) : d144 p ≤ (0 : Int) + d4171 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d144, d4171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2387 p hg
    simpa only [d144, d4171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d144, d4171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d144, d4171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2389 (p : Pattern) (guard : d4148 p = 1) : d145 p ≤ (0 : Int) + d4172 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d145, d4172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2385 p hg
    simpa only [d145, d4172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d145, d4172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2388 p hg
    simpa only [d145, d4172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2390 (p : Pattern) (guard : d4148 p = 1) : d146 p ≤ (0 : Int) + d4173 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d146, d4173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2378 p hg
    simpa only [d146, d4173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d146, d4173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2389 p hg
    simpa only [d146, d4173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2391 (p : Pattern) (guard : d4149 p = 1) : d147 p ≤ (0 : Int) + d4173 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d4149, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2390 p hg
    simpa only [d4149, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2392 (p : Pattern) (guard : d0 p = 1) : d152 p ≤ (0 : Int) + d4176 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2393 (p : Pattern) (guard : d1 p = 1) : d148 p ≤ (0 : Int) + d148 p := by
  omega
theorem compare2394 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2395 (p : Pattern) (guard : d4148 p = 1) : d153 p ≤ (0 : Int) + d148 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2393 p hg
    simpa only [d4148, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2394 p hg
    simpa only [d4148, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2396 (p : Pattern) (guard : d4148 p = 1) : d154 p ≤ (0 : Int) + d4174 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d154, d4174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2395 p hg
    simpa only [d154, d4174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d154, d4174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d154, d4174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2397 (p : Pattern) (guard : d4148 p = 1) : d155 p ≤ (0 : Int) + d4175 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d155, d4175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2396 p hg
    simpa only [d155, d4175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d155, d4175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d155, d4175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2398 (p : Pattern) (guard : d4148 p = 1) : d156 p ≤ (0 : Int) + d4176 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d156, d4176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2378 p hg
    simpa only [d156, d4176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d156, d4176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2397 p hg
    simpa only [d156, d4176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2399 (p : Pattern) (guard : d4149 p = 1) : d157 p ≤ (0 : Int) + d4176 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2392 p hg
    simpa only [d4149, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2398 p hg
    simpa only [d4149, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2400 (p : Pattern) (guard : d4149 p = 1) : d158 p ≤ (0 : Int) + d4177 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d158, d4177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2391 p hg
    simpa only [d158, d4177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d158, d4177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2399 p hg
    simpa only [d158, d4177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2401 (p : Pattern) (guard : d0 p = 1) : d161 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2402 (p : Pattern) (guard : d4149 p = 1) : d162 p ≤ (0 : Int) + d12 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2401 p hg
    simpa only [d4149, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d4149, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2403 (p : Pattern) (guard : d4149 p = 1) : d163 p ≤ (0 : Int) + d4178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d163, d4178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2399 p hg
    simpa only [d163, d4178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d163, d4178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2402 p hg
    simpa only [d163, d4178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2404 (p : Pattern) (guard : d4149 p = 1) : d164 p ≤ (0 : Int) + d4179 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d164, d4179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2400 p hg
    simpa only [d164, d4179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d164, d4179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2403 p hg
    simpa only [d164, d4179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2405 (p : Pattern) (guard : d4149 p = 1) : d165 p ≤ (0 : Int) + d4178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d165, d4178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2399 p hg
    simpa only [d165, d4178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d165, d4178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2364 p hg
    simpa only [d165, d4178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2406 (p : Pattern) (guard : d4149 p = 1) : d166 p ≤ (0 : Int) + d4179 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d166, d4179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2400 p hg
    simpa only [d166, d4179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d166, d4179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2405 p hg
    simpa only [d166, d4179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2407 (p : Pattern) (guard : d4149 p = 1) : d167 p ≤ (0 : Int) + d4179 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2404 p hg
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2406 p hg
    simpa only [d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2408 (p : Pattern) (guard : d4149 p = 1) : d168 p ≤ (0 : Int) + d4180 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d168, d4180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2367 p hg
    simpa only [d168, d4180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d168, d4180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2407 p hg
    simpa only [d168, d4180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2409 (p : Pattern) (guard : d4149 p = 1) : d169 p ≤ (0 : Int) + d4181 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d169, d4181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2367 p hg
    simpa only [d169, d4181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d169, d4181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2408 p hg
    simpa only [d169, d4181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2410 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2411 (p : Pattern) (guard : d4148 p = 1) : d211 p ≤ (0 : Int) + d109 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2371 p hg
    simpa only [d4148, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2410 p hg
    simpa only [d4148, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2412 (p : Pattern) (guard : d4148 p = 1) : d212 p ≤ (0 : Int) + d4168 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d212, d4168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2370 p hg
    simpa only [d212, d4168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d212, d4168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2411 p hg
    simpa only [d212, d4168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2413 (p : Pattern) (guard : d4148 p = 1) : d213 p ≤ (0 : Int) + d1140 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d213, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2411 p hg
    simpa only [d213, d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d213, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d213, d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2414 (p : Pattern) (guard : d4148 p = 1) : d214 p ≤ (0 : Int) + d4169 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d214, d4169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2412 p hg
    simpa only [d214, d4169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d214, d4169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2413 p hg
    simpa only [d214, d4169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2415 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d125 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2416 (p : Pattern) (guard : d4148 p = 1) : d215 p ≤ (0 : Int) + d125 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2382 p hg
    simpa only [d4148, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2415 p hg
    simpa only [d4148, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2417 (p : Pattern) (guard : d4148 p = 1) : d216 p ≤ (0 : Int) + d4170 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d216, d4170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2381 p hg
    simpa only [d216, d4170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d216, d4170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2416 p hg
    simpa only [d216, d4170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2418 (p : Pattern) (guard : d4148 p = 1) : d217 p ≤ (0 : Int) + d4171 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d217, d4171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2416 p hg
    simpa only [d217, d4171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d217, d4171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d217, d4171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2419 (p : Pattern) (guard : d4148 p = 1) : d218 p ≤ (0 : Int) + d4172 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d218, d4172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2417 p hg
    simpa only [d218, d4172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d218, d4172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2418 p hg
    simpa only [d218, d4172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2420 (p : Pattern) (guard : d4148 p = 1) : d219 p ≤ (0 : Int) + d4173 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d219, d4173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2414 p hg
    simpa only [d219, d4173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d219, d4173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2419 p hg
    simpa only [d219, d4173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2421 (p : Pattern) (guard : d4149 p = 1) : d220 p ≤ (0 : Int) + d4173 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d4149, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2420 p hg
    simpa only [d4149, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2422 (p : Pattern) (guard : d4148 p = 1) : d221 p ≤ (0 : Int) + d4176 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d221, d4176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2414 p hg
    simpa only [d221, d4176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d221, d4176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2397 p hg
    simpa only [d221, d4176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2423 (p : Pattern) (guard : d4149 p = 1) : d222 p ≤ (0 : Int) + d4176 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2392 p hg
    simpa only [d4149, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2422 p hg
    simpa only [d4149, d222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2424 (p : Pattern) (guard : d4149 p = 1) : d223 p ≤ (0 : Int) + d4177 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d223, d4177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2421 p hg
    simpa only [d223, d4177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d223, d4177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2423 p hg
    simpa only [d223, d4177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2425 (p : Pattern) (guard : d4149 p = 1) : d224 p ≤ (0 : Int) + d4178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d224, d4178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2423 p hg
    simpa only [d224, d4178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d224, d4178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2402 p hg
    simpa only [d224, d4178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2426 (p : Pattern) (guard : d4149 p = 1) : d225 p ≤ (0 : Int) + d4179 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d225, d4179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2424 p hg
    simpa only [d225, d4179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d225, d4179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2425 p hg
    simpa only [d225, d4179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2427 (p : Pattern) (guard : d0 p = 1) : d281 p ≤ (0 : Int) + d4185 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2428 (p : Pattern) (guard : d1 p = 1) : d270 p ≤ (0 : Int) + d270 p := by
  omega
theorem compare2429 (p : Pattern) (guard : d0 p = 1) : d283 p ≤ (0 : Int) + d270 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2430 (p : Pattern) (guard : d4148 p = 1) : d284 p ≤ (0 : Int) + d270 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2428 p hg
    simpa only [d4148, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2429 p hg
    simpa only [d4148, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2431 (p : Pattern) (guard : d1 p = 1) : d274 p ≤ (0 : Int) + d274 p := by
  omega
theorem compare2432 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d274 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2433 (p : Pattern) (guard : d4148 p = 1) : d285 p ≤ (0 : Int) + d274 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2431 p hg
    simpa only [d4148, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2432 p hg
    simpa only [d4148, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2434 (p : Pattern) (guard : d4148 p = 1) : d286 p ≤ (0 : Int) + d4182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d286, d4182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2430 p hg
    simpa only [d286, d4182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d286, d4182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2433 p hg
    simpa only [d286, d4182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2435 (p : Pattern) (guard : d4148 p = 1) : d287 p ≤ (0 : Int) + d4183 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d287, d4183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2433 p hg
    simpa only [d287, d4183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d287, d4183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d287, d4183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2436 (p : Pattern) (guard : d4148 p = 1) : d288 p ≤ (0 : Int) + d4184 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d288, d4184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2434 p hg
    simpa only [d288, d4184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d288, d4184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2435 p hg
    simpa only [d288, d4184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2437 (p : Pattern) (guard : d4148 p = 1) : d289 p ≤ (0 : Int) + d4185 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d289, d4185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2414 p hg
    simpa only [d289, d4185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d289, d4185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2436 p hg
    simpa only [d289, d4185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2438 (p : Pattern) (guard : d4149 p = 1) : d290 p ≤ (0 : Int) + d4185 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2427 p hg
    simpa only [d4149, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2437 p hg
    simpa only [d4149, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2439 (p : Pattern) (guard : d0 p = 1) : d297 p ≤ (0 : Int) + d4189 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2440 (p : Pattern) (guard : d1 p = 1) : d269 p ≤ (0 : Int) + d269 p := by
  omega
theorem compare2441 (p : Pattern) (guard : d0 p = 1) : d298 p ≤ (0 : Int) + d269 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2442 (p : Pattern) (guard : d4148 p = 1) : d299 p ≤ (0 : Int) + d269 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d4148, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2441 p hg
    simpa only [d4148, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2443 (p : Pattern) (guard : d1 p = 1) : d292 p ≤ (0 : Int) + d292 p := by
  omega
theorem compare2444 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d292 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2445 (p : Pattern) (guard : d4148 p = 1) : d300 p ≤ (0 : Int) + d292 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2443 p hg
    simpa only [d4148, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2444 p hg
    simpa only [d4148, d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2446 (p : Pattern) (guard : d4148 p = 1) : d301 p ≤ (0 : Int) + d4186 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d301, d4186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2442 p hg
    simpa only [d301, d4186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d301, d4186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2445 p hg
    simpa only [d301, d4186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2447 (p : Pattern) (guard : d4148 p = 1) : d302 p ≤ (0 : Int) + d4187 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d302, d4187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2445 p hg
    simpa only [d302, d4187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d302, d4187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d302, d4187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2448 (p : Pattern) (guard : d4148 p = 1) : d303 p ≤ (0 : Int) + d4188 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d303, d4188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2446 p hg
    simpa only [d303, d4188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d303, d4188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2447 p hg
    simpa only [d303, d4188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2449 (p : Pattern) (guard : d4148 p = 1) : d304 p ≤ (0 : Int) + d4189 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d304, d4189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2448 p hg
    simpa only [d304, d4189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d304, d4189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2397 p hg
    simpa only [d304, d4189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2450 (p : Pattern) (guard : d4149 p = 1) : d305 p ≤ (0 : Int) + d4189 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2439 p hg
    simpa only [d4149, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2449 p hg
    simpa only [d4149, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2451 (p : Pattern) (guard : d4149 p = 1) : d306 p ≤ (0 : Int) + d4190 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d306, d4190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2438 p hg
    simpa only [d306, d4190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d306, d4190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2450 p hg
    simpa only [d306, d4190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2452 (p : Pattern) (guard : d4149 p = 1) : d307 p ≤ (0 : Int) + d4191 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d307, d4191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2450 p hg
    simpa only [d307, d4191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d307, d4191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2364 p hg
    simpa only [d307, d4191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2453 (p : Pattern) (guard : d4149 p = 1) : d308 p ≤ (0 : Int) + d4192 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d308, d4192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2451 p hg
    simpa only [d308, d4192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d308, d4192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2452 p hg
    simpa only [d308, d4192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2454 (p : Pattern) (guard : d4149 p = 1) : d309 p ≤ (0 : Int) + d4193 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d309, d4193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2426 p hg
    simpa only [d309, d4193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d309, d4193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2453 p hg
    simpa only [d309, d4193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2455 (p : Pattern) (guard : d4149 p = 1) : d310 p ≤ (0 : Int) + d4194 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d310, d4194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2367 p hg
    simpa only [d310, d4194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d310, d4194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d310, d4194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2456 (p : Pattern) (guard : d4149 p = 1) : d311 p ≤ (0 : Int) + d4195 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d311, d4195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2367 p hg
    simpa only [d311, d4195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d311, d4195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2455 p hg
    simpa only [d311, d4195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2457 (p : Pattern) (guard : d4149 p = 1) : d312 p ≤ (0 : Int) + d4196 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d312, d4196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2409 p hg
    simpa only [d312, d4196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d312, d4196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2456 p hg
    simpa only [d312, d4196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2458 (p : Pattern) (guard : d1 p = 1) : d267 p ≤ (2 : Int) + d267 p := by
  omega
theorem compare2459 (p : Pattern) (guard : d0 p = 1) : d400 p ≤ (0 : Int) + d87 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2460 (p : Pattern) (guard : d4068 p = 1) : d517 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d517, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1896 p hg
    simpa only [d4068, d517, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d517, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2459 p hg
    simpa only [d4068, d517, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2461 (p : Pattern) (guard : d0 p = 1) : d544 p ≤ (0 : Int) + d413 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2462 (p : Pattern) (guard : d4113 p = 1) : d545 p ≤ (0 : Int) + d499 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d545, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2460 p hg
    simpa only [d4113, d545, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d545, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2461 p hg
    simpa only [d4113, d545, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2463 (p : Pattern) (guard : d0 p = 1) : d422 p ≤ (0 : Int) + d87 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2464 (p : Pattern) (guard : d4068 p = 1) : d546 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d546, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1896 p hg
    simpa only [d4068, d546, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d546, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2463 p hg
    simpa only [d4068, d546, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2465 (p : Pattern) (guard : d0 p = 1) : d547 p ≤ (0 : Int) + d425 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2466 (p : Pattern) (guard : d4113 p = 1) : d548 p ≤ (0 : Int) + d500 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d548, d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2464 p hg
    simpa only [d4113, d548, d500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d548, d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2465 p hg
    simpa only [d4113, d548, d500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2467 (p : Pattern) (guard : d4113 p = 1) : d549 p ≤ (0 : Int) + d501 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d549, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2462 p hg
    simpa only [d549, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d549, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2466 p hg
    simpa only [d549, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2468 (p : Pattern) (guard : d0 p = 1) : d439 p ≤ (0 : Int) + d87 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2469 (p : Pattern) (guard : d4068 p = 1) : d550 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d550, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1896 p hg
    simpa only [d4068, d550, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d550, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2468 p hg
    simpa only [d4068, d550, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2470 (p : Pattern) (guard : d0 p = 1) : d551 p ≤ (0 : Int) + d442 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2471 (p : Pattern) (guard : d4113 p = 1) : d552 p ≤ (0 : Int) + d502 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d552, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2469 p hg
    simpa only [d4113, d552, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d552, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2470 p hg
    simpa only [d4113, d552, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2472 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (0 : Int) + d87 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2473 (p : Pattern) (guard : d4068 p = 1) : d553 p ≤ (0 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d553, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1896 p hg
    simpa only [d4068, d553, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d553, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2472 p hg
    simpa only [d4068, d553, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2474 (p : Pattern) (guard : d0 p = 1) : d547 p ≤ (0 : Int) + d444 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2475 (p : Pattern) (guard : d4113 p = 1) : d554 p ≤ (0 : Int) + d503 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d554, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2473 p hg
    simpa only [d4113, d554, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d554, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2474 p hg
    simpa only [d4113, d554, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2476 (p : Pattern) (guard : d4113 p = 1) : d555 p ≤ (0 : Int) + d504 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d555, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2471 p hg
    simpa only [d555, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d555, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d555, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2477 (p : Pattern) (guard : d4113 p = 1) : d556 p ≤ (0 : Int) + d505 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d556, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2467 p hg
    simpa only [d556, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d556, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2476 p hg
    simpa only [d556, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2478 (p : Pattern) (guard : d0 p = 1) : d439 p ≤ (0 : Int) + d157 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2479 (p : Pattern) (guard : d4068 p = 1) : d557 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d557, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1910 p hg
    simpa only [d4068, d557, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d557, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2478 p hg
    simpa only [d4068, d557, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2480 (p : Pattern) (guard : d0 p = 1) : d580 p ≤ (0 : Int) + d442 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2481 (p : Pattern) (guard : d4113 p = 1) : d581 p ≤ (0 : Int) + d506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d581, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2479 p hg
    simpa only [d4113, d581, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d581, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d4113, d581, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2482 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (0 : Int) + d157 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2483 (p : Pattern) (guard : d4068 p = 1) : d582 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d582, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1910 p hg
    simpa only [d4068, d582, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d582, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d4068, d582, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2484 (p : Pattern) (guard : d0 p = 1) : d583 p ≤ (0 : Int) + d444 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2485 (p : Pattern) (guard : d4113 p = 1) : d584 p ≤ (0 : Int) + d507 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d584, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2483 p hg
    simpa only [d4113, d584, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d584, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2484 p hg
    simpa only [d4113, d584, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2486 (p : Pattern) (guard : d4113 p = 1) : d585 p ≤ (0 : Int) + d508 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d585, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d585, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d585, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d585, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2487 (p : Pattern) (guard : d4113 p = 1) : d586 p ≤ (0 : Int) + d509 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d586, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2467 p hg
    simpa only [d586, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d586, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d586, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2488 (p : Pattern) (guard : d4113 p = 1) : d587 p ≤ (0 : Int) + d510 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d587, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2477 p hg
    simpa only [d587, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d587, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2487 p hg
    simpa only [d587, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2489 (p : Pattern) (guard : d0 p = 1) : d606 p ≤ (0 : Int) + d444 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2490 (p : Pattern) (guard : d4113 p = 1) : d607 p ≤ (0 : Int) + d503 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d607, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2473 p hg
    simpa only [d4113, d607, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d607, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2489 p hg
    simpa only [d4113, d607, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2491 (p : Pattern) (guard : d4113 p = 1) : d608 p ≤ (0 : Int) + d504 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d608, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2471 p hg
    simpa only [d608, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d608, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2490 p hg
    simpa only [d608, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2492 (p : Pattern) (guard : d4113 p = 1) : d609 p ≤ (0 : Int) + d505 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d609, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2467 p hg
    simpa only [d609, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d609, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d609, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2493 (p : Pattern) (guard : d0 p = 1) : d457 p ≤ (0 : Int) + d222 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2494 (p : Pattern) (guard : d4068 p = 1) : d610 p ≤ (0 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d610, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1922 p hg
    simpa only [d4068, d610, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d610, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2493 p hg
    simpa only [d4068, d610, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2495 (p : Pattern) (guard : d0 p = 1) : d617 p ≤ (0 : Int) + d463 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2496 (p : Pattern) (guard : d4113 p = 1) : d618 p ≤ (0 : Int) + d511 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d618, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2494 p hg
    simpa only [d4113, d618, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d618, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2495 p hg
    simpa only [d4113, d618, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2497 (p : Pattern) (guard : d0 p = 1) : d473 p ≤ (0 : Int) + d305 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2498 (p : Pattern) (guard : d4068 p = 1) : d619 p ≤ (0 : Int) + d306 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d619, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1988 p hg
    simpa only [d4068, d619, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d619, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2497 p hg
    simpa only [d4068, d619, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2499 (p : Pattern) (guard : d0 p = 1) : d647 p ≤ (0 : Int) + d476 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2500 (p : Pattern) (guard : d4113 p = 1) : d648 p ≤ (0 : Int) + d512 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4068 p = 1 := by simpa only [d4113, d648, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2498 p hg
    simpa only [d4113, d648, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4113, d648, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d4113, d648, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2501 (p : Pattern) (guard : d4113 p = 1) : d649 p ≤ (0 : Int) + d513 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d649, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2496 p hg
    simpa only [d649, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d649, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2500 p hg
    simpa only [d649, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2502 (p : Pattern) (guard : d4113 p = 1) : d650 p ≤ (0 : Int) + d514 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d650, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2467 p hg
    simpa only [d650, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d650, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2501 p hg
    simpa only [d650, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2503 (p : Pattern) (guard : d4113 p = 1) : d651 p ≤ (0 : Int) + d515 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d651, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2492 p hg
    simpa only [d651, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d651, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2502 p hg
    simpa only [d651, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2504 (p : Pattern) (guard : d4113 p = 1) : d652 p ≤ (0 : Int) + d516 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4113 p = 1 := by simpa only [d652, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d652, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4113 p = 1 := by simpa only [d652, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d652, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2505 (p : Pattern) (guard : d0 p = 1) : d517 p ≤ (4 : Int) + d88 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2506 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (4 : Int) + d29 p := by
  omega
theorem compare2507 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (4 : Int) + d14 p := by
  omega
theorem compare2508 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (4 : Int) + d0 p := by
  change (4 : Int) ≤ (4 : Int) + 0
  decide
theorem compare2509 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d12 p := by
  omega
theorem compare2510 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (4 : Int) + d13 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2508 p hg
    simpa only [d17, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d17, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2511 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (4 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2508 p hg
    simpa only [d18, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2510 p hg
    simpa only [d18, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2512 (p : Pattern) (guard : d1 p = 1) : d518 p ≤ (4 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2507 p hg
    simpa only [d518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2511 p hg
    simpa only [d518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2513 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (4 : Int) + d2 p := by
  change (6 : Int) ≤ (4 : Int) + 2
  decide
theorem compare2514 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (4 : Int) + d30 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2513 p hg
    simpa only [d34, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d34, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2515 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (4 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2513 p hg
    simpa only [d35, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2514 p hg
    simpa only [d35, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2516 (p : Pattern) (guard : d1 p = 1) : d36 p ≤ (4 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2515 p hg
    simpa only [d36, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d36, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2517 (p : Pattern) (guard : d1 p = 1) : d519 p ≤ (4 : Int) + d33 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d519, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2512 p hg
    simpa only [d519, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d519, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2516 p hg
    simpa only [d519, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2518 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (4 : Int) + d6 p := by
  change (10 : Int) ≤ (4 : Int) + 6
  decide
theorem compare2519 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (4 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2518 p hg
    simpa only [d57, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d57, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
