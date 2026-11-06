/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons016
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2380 (p : Pattern) (guard : d1047 p = 1) : d65 p ≤ (0 : Int) + d65 p := by
  omega
theorem compare2381 (p : Pattern) (guard : d1047 p = 1) : d230 p ≤ (0 : Int) + d510 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d230, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2372 p hg
    simpa only [d230, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d230, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2380 p hg
    simpa only [d230, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2382 (p : Pattern) (guard : d1047 p = 1) : d231 p ≤ (0 : Int) + d511 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d231, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2379 p hg
    simpa only [d231, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d231, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2381 p hg
    simpa only [d231, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2383 (p : Pattern) (guard : d1047 p = 1) : d229 p ≤ (0 : Int) + d512 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d229, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2374 p hg
    simpa only [d229, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d229, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2378 p hg
    simpa only [d229, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2384 (p : Pattern) (guard : d1047 p = 1) : d230 p ≤ (0 : Int) + d513 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d230, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2375 p hg
    simpa only [d230, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d230, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2380 p hg
    simpa only [d230, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2385 (p : Pattern) (guard : d1047 p = 1) : d231 p ≤ (0 : Int) + d514 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d231, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2383 p hg
    simpa only [d231, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d231, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2384 p hg
    simpa only [d231, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2386 (p : Pattern) (guard : d1047 p = 1) : d231 p ≤ (0 : Int) + d515 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2382 p hg
    simpa only [d515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2385 p hg
    simpa only [d515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2387 (p : Pattern) (guard : d1047 p = 1) : d366 p ≤ (0 : Int) + d516 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d366, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2377 p hg
    simpa only [d366, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d366, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2386 p hg
    simpa only [d366, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2388 (p : Pattern) (guard : d1047 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare2389 (p : Pattern) (guard : d1047 p = 1) : d367 p ≤ (0 : Int) + d517 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d367, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2386 p hg
    simpa only [d367, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d367, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2388 p hg
    simpa only [d367, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2390 (p : Pattern) (guard : d1047 p = 1) : d368 p ≤ (0 : Int) + d518 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d368, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2387 p hg
    simpa only [d368, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d368, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2389 p hg
    simpa only [d368, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2391 (p : Pattern) (guard : d1047 p = 1) : d369 p ≤ (0 : Int) + d519 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d369, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2373 p hg
    simpa only [d369, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d369, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2388 p hg
    simpa only [d369, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2392 (p : Pattern) (guard : d1047 p = 1) : d370 p ≤ (0 : Int) + d520 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d370, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2382 p hg
    simpa only [d370, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d370, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2388 p hg
    simpa only [d370, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2393 (p : Pattern) (guard : d1047 p = 1) : d371 p ≤ (0 : Int) + d521 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d371, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2391 p hg
    simpa only [d371, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d371, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2392 p hg
    simpa only [d371, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2394 (p : Pattern) (guard : d1047 p = 1) : d372 p ≤ (0 : Int) + d522 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d372, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2392 p hg
    simpa only [d372, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d372, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2388 p hg
    simpa only [d372, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2395 (p : Pattern) (guard : d1047 p = 1) : d373 p ≤ (0 : Int) + d523 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d373, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2393 p hg
    simpa only [d373, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d373, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2394 p hg
    simpa only [d373, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2396 (p : Pattern) (guard : d1047 p = 1) : d374 p ≤ (0 : Int) + d524 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d374, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2390 p hg
    simpa only [d374, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d374, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2395 p hg
    simpa only [d374, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2397 (p : Pattern) (guard : d829 p = 1) : d7 p ≤ (0 : Int) + d7 p := by
  omega
theorem compare2398 (p : Pattern) (guard : d1016 p = 1) : d106 p ≤ (0 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2397 p hg
    simpa only [d1016, d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1656 p hg
    simpa only [d1016, d106, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2399 (p : Pattern) (guard : d1050 p = 1) : d106 p ≤ (0 : Int) + d57 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2169 p hg
    simpa only [d1050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2398 p hg
    simpa only [d1050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2400 (p : Pattern) (guard : d829 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare2401 (p : Pattern) (guard : d1016 p = 1) : d109 p ≤ (0 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2400 p hg
    simpa only [d1016, d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1664 p hg
    simpa only [d1016, d109, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2402 (p : Pattern) (guard : d1050 p = 1) : d109 p ≤ (0 : Int) + d63 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2170 p hg
    simpa only [d1050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2401 p hg
    simpa only [d1050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2403 (p : Pattern) (guard : d1050 p = 1) : d227 p ≤ (0 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d227, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2399 p hg
    simpa only [d227, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d227, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2402 p hg
    simpa only [d227, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2404 (p : Pattern) (guard : d1050 p = 1) : d106 p ≤ (0 : Int) + d106 p := by
  omega
theorem compare2405 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (0 : Int) + d119 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2406 (p : Pattern) (guard : d829 p = 1) : d7 p ≤ (0 : Int) + d120 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d829, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2405 p hg
    simpa only [d829, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2407 (p : Pattern) (guard : d1016 p = 1) : d106 p ≤ (0 : Int) + d121 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d106, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2406 p hg
    simpa only [d1016, d106, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d106, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d1016, d106, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2408 (p : Pattern) (guard : d1050 p = 1) : d106 p ≤ (0 : Int) + d122 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d1050, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare690 p hg
    simpa only [d1050, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d1050, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2407 p hg
    simpa only [d1050, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2409 (p : Pattern) (guard : d1050 p = 1) : d106 p ≤ (0 : Int) + d179 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2404 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2408 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2410 (p : Pattern) (guard : d1050 p = 1) : d109 p ≤ (0 : Int) + d109 p := by
  omega
theorem compare2411 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (0 : Int) + d125 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2412 (p : Pattern) (guard : d829 p = 1) : d11 p ≤ (0 : Int) + d126 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare295 p hg
    simpa only [d829, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2411 p hg
    simpa only [d829, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2413 (p : Pattern) (guard : d829 p = 1) : d12 p ≤ (0 : Int) + d127 p := by
  cases selected : p 168 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d12, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2406 p hg
    simpa only [d12, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d12, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2412 p hg
    simpa only [d12, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2414 (p : Pattern) (guard : d1016 p = 1) : d109 p ≤ (0 : Int) + d128 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d109, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2413 p hg
    simpa only [d1016, d109, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d109, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d1016, d109, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2415 (p : Pattern) (guard : d1050 p = 1) : d109 p ≤ (0 : Int) + d129 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d1050, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare695 p hg
    simpa only [d1050, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d1050, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2414 p hg
    simpa only [d1050, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2416 (p : Pattern) (guard : d1050 p = 1) : d109 p ≤ (0 : Int) + d237 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2410 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2415 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2417 (p : Pattern) (guard : d1050 p = 1) : d227 p ≤ (0 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d227, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2409 p hg
    simpa only [d227, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d227, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2416 p hg
    simpa only [d227, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2418 (p : Pattern) (guard : d1050 p = 1) : d227 p ≤ (0 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2403 p hg
    simpa only [d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2417 p hg
    simpa only [d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2419 (p : Pattern) (guard : d1050 p = 1) : d55 p ≤ (0 : Int) + d55 p := by
  omega
theorem compare2420 (p : Pattern) (guard : d1050 p = 1) : d229 p ≤ (0 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d229, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2399 p hg
    simpa only [d229, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d229, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2419 p hg
    simpa only [d229, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2421 (p : Pattern) (guard : d1050 p = 1) : d65 p ≤ (0 : Int) + d65 p := by
  omega
theorem compare2422 (p : Pattern) (guard : d1050 p = 1) : d230 p ≤ (0 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d230, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2402 p hg
    simpa only [d230, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d230, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2421 p hg
    simpa only [d230, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2423 (p : Pattern) (guard : d1050 p = 1) : d231 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d231, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2420 p hg
    simpa only [d231, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d231, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2422 p hg
    simpa only [d231, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2424 (p : Pattern) (guard : d1050 p = 1) : d229 p ≤ (0 : Int) + d181 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d229, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2408 p hg
    simpa only [d229, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d229, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2419 p hg
    simpa only [d229, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2425 (p : Pattern) (guard : d1050 p = 1) : d230 p ≤ (0 : Int) + d240 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d230, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2415 p hg
    simpa only [d230, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d230, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2421 p hg
    simpa only [d230, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2426 (p : Pattern) (guard : d1050 p = 1) : d231 p ≤ (0 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d231, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2424 p hg
    simpa only [d231, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d231, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2425 p hg
    simpa only [d231, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2427 (p : Pattern) (guard : d1050 p = 1) : d231 p ≤ (0 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2423 p hg
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2426 p hg
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2428 (p : Pattern) (guard : d1050 p = 1) : d366 p ≤ (0 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d366, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2418 p hg
    simpa only [d366, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d366, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2427 p hg
    simpa only [d366, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2429 (p : Pattern) (guard : d1050 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare2430 (p : Pattern) (guard : d1050 p = 1) : d367 p ≤ (0 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d367, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2427 p hg
    simpa only [d367, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d367, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2429 p hg
    simpa only [d367, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2431 (p : Pattern) (guard : d1050 p = 1) : d368 p ≤ (0 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d368, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2428 p hg
    simpa only [d368, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d368, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2430 p hg
    simpa only [d368, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2432 (p : Pattern) (guard : d1016 p = 1) : d106 p ≤ (0 : Int) + d139 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d106, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2406 p hg
    simpa only [d1016, d106, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d106, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2216 p hg
    simpa only [d1016, d106, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2433 (p : Pattern) (guard : d1050 p = 1) : d106 p ≤ (0 : Int) + d153 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d1050, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2169 p hg
    simpa only [d1050, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d1050, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2432 p hg
    simpa only [d1050, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2434 (p : Pattern) (guard : d1050 p = 1) : d106 p ≤ (0 : Int) + d186 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2399 p hg
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2433 p hg
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2435 (p : Pattern) (guard : d1016 p = 1) : d109 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d109, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2413 p hg
    simpa only [d1016, d109, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d109, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2220 p hg
    simpa only [d1016, d109, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2436 (p : Pattern) (guard : d1050 p = 1) : d109 p ≤ (0 : Int) + d155 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d1050, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2170 p hg
    simpa only [d1050, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d1050, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2435 p hg
    simpa only [d1050, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2437 (p : Pattern) (guard : d1050 p = 1) : d109 p ≤ (0 : Int) + d246 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2402 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2436 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2438 (p : Pattern) (guard : d1050 p = 1) : d227 p ≤ (0 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d227, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2434 p hg
    simpa only [d227, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d227, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2437 p hg
    simpa only [d227, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2439 (p : Pattern) (guard : d1050 p = 1) : d369 p ≤ (0 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d369, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2438 p hg
    simpa only [d369, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d369, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2429 p hg
    simpa only [d369, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2440 (p : Pattern) (guard : d1050 p = 1) : d106 p ≤ (0 : Int) + d140 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d1050, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2308 p hg
    simpa only [d1050, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d1050, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2432 p hg
    simpa only [d1050, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2441 (p : Pattern) (guard : d1050 p = 1) : d229 p ≤ (0 : Int) + d188 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d229, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d229, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d229, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2419 p hg
    simpa only [d229, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2442 (p : Pattern) (guard : d1050 p = 1) : d109 p ≤ (0 : Int) + d147 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d1050, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2311 p hg
    simpa only [d1050, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d1050, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2435 p hg
    simpa only [d1050, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2443 (p : Pattern) (guard : d1050 p = 1) : d230 p ≤ (0 : Int) + d249 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d230, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2442 p hg
    simpa only [d230, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d230, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2421 p hg
    simpa only [d230, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2444 (p : Pattern) (guard : d1050 p = 1) : d231 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d231, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2441 p hg
    simpa only [d231, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d231, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2443 p hg
    simpa only [d231, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2445 (p : Pattern) (guard : d1050 p = 1) : d370 p ≤ (0 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d370, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2444 p hg
    simpa only [d370, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d370, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2429 p hg
    simpa only [d370, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2446 (p : Pattern) (guard : d1050 p = 1) : d371 p ≤ (0 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d371, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2439 p hg
    simpa only [d371, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d371, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2445 p hg
    simpa only [d371, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2447 (p : Pattern) (guard : d1050 p = 1) : d229 p ≤ (0 : Int) + d191 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d229, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2433 p hg
    simpa only [d229, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d229, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2419 p hg
    simpa only [d229, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2448 (p : Pattern) (guard : d1050 p = 1) : d230 p ≤ (0 : Int) + d253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d230, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2436 p hg
    simpa only [d230, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d230, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2421 p hg
    simpa only [d230, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2449 (p : Pattern) (guard : d1050 p = 1) : d231 p ≤ (0 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d231, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2447 p hg
    simpa only [d231, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d231, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2448 p hg
    simpa only [d231, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2450 (p : Pattern) (guard : d1050 p = 1) : d370 p ≤ (0 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d370, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2449 p hg
    simpa only [d370, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d370, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2429 p hg
    simpa only [d370, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2451 (p : Pattern) (guard : d1050 p = 1) : d372 p ≤ (0 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d372, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2450 p hg
    simpa only [d372, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d372, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2429 p hg
    simpa only [d372, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2452 (p : Pattern) (guard : d1050 p = 1) : d373 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d373, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2446 p hg
    simpa only [d373, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d373, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2451 p hg
    simpa only [d373, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2453 (p : Pattern) (guard : d1050 p = 1) : d374 p ≤ (0 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1050 p = 1 := by simpa only [d374, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2431 p hg
    simpa only [d374, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1050 p = 1 := by simpa only [d374, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2452 p hg
    simpa only [d374, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2454 (p : Pattern) (guard : d851 p = 1) : d55 p ≤ (0 : Int) + d55 p := by
  omega
theorem compare2455 (p : Pattern) (guard : d851 p = 1) : d56 p ≤ (0 : Int) + d137 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d56, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d56, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d56, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d56, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2456 (p : Pattern) (guard : d851 p = 1) : d57 p ≤ (0 : Int) + d501 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d57, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d57, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d57, d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2455 p hg
    simpa only [d57, d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2457 (p : Pattern) (guard : d851 p = 1) : d60 p ≤ (0 : Int) + d60 p := by
  omega
theorem compare2458 (p : Pattern) (guard : d851 p = 1) : d61 p ≤ (0 : Int) + d143 p := by
  cases selected : p 186 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d61, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2370 p hg
    simpa only [d61, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d61, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2457 p hg
    simpa only [d61, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2459 (p : Pattern) (guard : d851 p = 1) : d62 p ≤ (0 : Int) + d144 p := by
  cases selected : p 168 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d62, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2455 p hg
    simpa only [d62, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d62, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2458 p hg
    simpa only [d62, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2460 (p : Pattern) (guard : d851 p = 1) : d63 p ≤ (0 : Int) + d503 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d63, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2371 p hg
    simpa only [d63, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d63, d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2459 p hg
    simpa only [d63, d503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2461 (p : Pattern) (guard : d851 p = 1) : d64 p ≤ (0 : Int) + d504 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d64, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2456 p hg
    simpa only [d64, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d64, d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2460 p hg
    simpa only [d64, d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2462 (p : Pattern) (guard : d851 p = 1) : d106 p ≤ (0 : Int) + d505 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d106, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2368 p hg
    simpa only [d106, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d106, d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d106, d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2463 (p : Pattern) (guard : d851 p = 1) : d65 p ≤ (0 : Int) + d65 p := by
  omega
theorem compare2464 (p : Pattern) (guard : d851 p = 1) : d109 p ≤ (0 : Int) + d506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d109, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2371 p hg
    simpa only [d109, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d109, d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2463 p hg
    simpa only [d109, d506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2465 (p : Pattern) (guard : d851 p = 1) : d227 p ≤ (0 : Int) + d507 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d227, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2462 p hg
    simpa only [d227, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d227, d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2464 p hg
    simpa only [d227, d507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2466 (p : Pattern) (guard : d851 p = 1) : d228 p ≤ (0 : Int) + d508 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d228, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2461 p hg
    simpa only [d228, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d228, d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2465 p hg
    simpa only [d228, d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2467 (p : Pattern) (guard : d851 p = 1) : d68 p ≤ (0 : Int) + d509 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d68, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2456 p hg
    simpa only [d68, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d68, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d68, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2468 (p : Pattern) (guard : d851 p = 1) : d69 p ≤ (0 : Int) + d510 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d69, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2460 p hg
    simpa only [d69, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d69, d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2463 p hg
    simpa only [d69, d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2469 (p : Pattern) (guard : d851 p = 1) : d70 p ≤ (0 : Int) + d511 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d70, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2467 p hg
    simpa only [d70, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d70, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2468 p hg
    simpa only [d70, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2470 (p : Pattern) (guard : d851 p = 1) : d229 p ≤ (0 : Int) + d512 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d229, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2462 p hg
    simpa only [d229, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d229, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2454 p hg
    simpa only [d229, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2471 (p : Pattern) (guard : d851 p = 1) : d230 p ≤ (0 : Int) + d513 p := by
  cases selected : p 158 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d230, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2464 p hg
    simpa only [d230, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d230, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2463 p hg
    simpa only [d230, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2472 (p : Pattern) (guard : d851 p = 1) : d231 p ≤ (0 : Int) + d514 p := by
  cases selected : p 141 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d231, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2470 p hg
    simpa only [d231, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d231, d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2471 p hg
    simpa only [d231, d514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2473 (p : Pattern) (guard : d851 p = 1) : d232 p ≤ (0 : Int) + d515 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d232, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2469 p hg
    simpa only [d232, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d232, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2472 p hg
    simpa only [d232, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2474 (p : Pattern) (guard : d851 p = 1) : d233 p ≤ (0 : Int) + d516 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d233, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2466 p hg
    simpa only [d233, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d233, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2473 p hg
    simpa only [d233, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2475 (p : Pattern) (guard : d851 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare2476 (p : Pattern) (guard : d851 p = 1) : d234 p ≤ (0 : Int) + d517 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d234, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2473 p hg
    simpa only [d234, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d234, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d234, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2477 (p : Pattern) (guard : d851 p = 1) : d235 p ≤ (0 : Int) + d518 p := by
  cases selected : p 132 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d235, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2474 p hg
    simpa only [d235, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d235, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2476 p hg
    simpa only [d235, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2478 (p : Pattern) (guard : d851 p = 1) : d67 p ≤ (0 : Int) + d519 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d67, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2461 p hg
    simpa only [d67, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d67, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d67, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2479 (p : Pattern) (guard : d851 p = 1) : d71 p ≤ (0 : Int) + d520 p := by
  cases selected : p 134 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d71, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2469 p hg
    simpa only [d71, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d71, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d71, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2480 (p : Pattern) (guard : d851 p = 1) : d72 p ≤ (0 : Int) + d521 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d72, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2478 p hg
    simpa only [d72, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d72, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2479 p hg
    simpa only [d72, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2481 (p : Pattern) (guard : d851 p = 1) : d73 p ≤ (0 : Int) + d522 p := by
  cases selected : p 133 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d73, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2479 p hg
    simpa only [d73, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d73, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2475 p hg
    simpa only [d73, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2482 (p : Pattern) (guard : d851 p = 1) : d74 p ≤ (0 : Int) + d523 p := by
  cases selected : p 132 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d74, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d74, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d74, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d74, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2483 (p : Pattern) (guard : d851 p = 1) : d236 p ≤ (0 : Int) + d524 p := by
  cases selected : p 108 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d236, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2477 p hg
    simpa only [d236, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d236, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d236, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2484 (p : Pattern) (guard : d850 p = 1) : d236 p ≤ (0 : Int) + d236 p := by
  omega
theorem compare2485 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (2 : Int) + d7 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare115 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare77 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2486 (p : Pattern) (guard : d757 p = 1) : d57 p ≤ (2 : Int) + d7 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d757, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare766 p hg
    simpa only [d757, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d757, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d757, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2487 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (2 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2488 (p : Pattern) (guard : d1014 p = 1) : d57 p ≤ (2 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2486 p hg
    simpa only [d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2487 p hg
    simpa only [d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2489 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (2 : Int) + d11 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare123 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare88 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2490 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (2 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2485 p hg
    simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2489 p hg
    simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2491 (p : Pattern) (guard : d757 p = 1) : d63 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d757, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare770 p hg
    simpa only [d757, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d757, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2490 p hg
    simpa only [d757, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2492 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2493 (p : Pattern) (guard : d1014 p = 1) : d63 p ≤ (2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2491 p hg
    simpa only [d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2492 p hg
    simpa only [d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2494 (p : Pattern) (guard : d1014 p = 1) : d64 p ≤ (2 : Int) + d13 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d64, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d64, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d64, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2493 p hg
    simpa only [d64, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2495 (p : Pattern) (guard : d757 p = 1) : d106 p ≤ (2 : Int) + d7 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d757, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare766 p hg
    simpa only [d757, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d757, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare77 p hg
    simpa only [d757, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2496 (p : Pattern) (guard : d0 p = 1) : d106 p ≤ (2 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2497 (p : Pattern) (guard : d1014 p = 1) : d106 p ≤ (2 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2495 p hg
    simpa only [d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2496 p hg
    simpa only [d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2498 (p : Pattern) (guard : d757 p = 1) : d109 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d757, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare770 p hg
    simpa only [d757, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d757, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare89 p hg
    simpa only [d757, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2499 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2500 (p : Pattern) (guard : d1014 p = 1) : d109 p ≤ (2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2498 p hg
    simpa only [d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2499 p hg
    simpa only [d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2501 (p : Pattern) (guard : d1014 p = 1) : d227 p ≤ (2 : Int) + d13 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d227, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2497 p hg
    simpa only [d227, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d227, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2500 p hg
    simpa only [d227, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2502 (p : Pattern) (guard : d1014 p = 1) : d228 p ≤ (2 : Int) + d13 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2494 p hg
    simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2501 p hg
    simpa only [d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2503 (p : Pattern) (guard : d1014 p = 1) : d55 p ≤ (2 : Int) + d55 p := by
  omega
theorem compare2504 (p : Pattern) (guard : d1014 p = 1) : d68 p ≤ (2 : Int) + d832 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d68, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2488 p hg
    simpa only [d68, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d68, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d68, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2505 (p : Pattern) (guard : d1014 p = 1) : d65 p ≤ (2 : Int) + d65 p := by
  omega
theorem compare2506 (p : Pattern) (guard : d1014 p = 1) : d69 p ≤ (2 : Int) + d833 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d69, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2493 p hg
    simpa only [d69, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d69, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2505 p hg
    simpa only [d69, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2507 (p : Pattern) (guard : d1014 p = 1) : d70 p ≤ (2 : Int) + d834 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d70, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2504 p hg
    simpa only [d70, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d70, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2506 p hg
    simpa only [d70, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2508 (p : Pattern) (guard : d1014 p = 1) : d229 p ≤ (2 : Int) + d832 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d229, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2497 p hg
    simpa only [d229, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d229, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2503 p hg
    simpa only [d229, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2509 (p : Pattern) (guard : d1014 p = 1) : d230 p ≤ (2 : Int) + d833 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d230, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2500 p hg
    simpa only [d230, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d230, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2505 p hg
    simpa only [d230, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2510 (p : Pattern) (guard : d1014 p = 1) : d231 p ≤ (2 : Int) + d834 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d231, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2508 p hg
    simpa only [d231, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d231, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d231, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2511 (p : Pattern) (guard : d1014 p = 1) : d232 p ≤ (2 : Int) + d834 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2507 p hg
    simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2510 p hg
    simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2512 (p : Pattern) (guard : d1014 p = 1) : d233 p ≤ (2 : Int) + d835 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d233, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2502 p hg
    simpa only [d233, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d233, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2511 p hg
    simpa only [d233, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2513 (p : Pattern) (guard : d1014 p = 1) : d66 p ≤ (2 : Int) + d66 p := by
  omega
theorem compare2514 (p : Pattern) (guard : d1014 p = 1) : d234 p ≤ (2 : Int) + d836 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d234, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2511 p hg
    simpa only [d234, d836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d234, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2513 p hg
    simpa only [d234, d836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2515 (p : Pattern) (guard : d1014 p = 1) : d235 p ≤ (2 : Int) + d837 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d235, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2512 p hg
    simpa only [d235, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d235, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2514 p hg
    simpa only [d235, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2516 (p : Pattern) (guard : d1014 p = 1) : d67 p ≤ (2 : Int) + d838 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d67, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2494 p hg
    simpa only [d67, d838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d67, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2513 p hg
    simpa only [d67, d838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2517 (p : Pattern) (guard : d1014 p = 1) : d71 p ≤ (2 : Int) + d839 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d71, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2507 p hg
    simpa only [d71, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d71, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2513 p hg
    simpa only [d71, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2518 (p : Pattern) (guard : d1014 p = 1) : d72 p ≤ (2 : Int) + d840 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d72, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2516 p hg
    simpa only [d72, d840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d72, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2517 p hg
    simpa only [d72, d840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2519 (p : Pattern) (guard : d1014 p = 1) : d73 p ≤ (2 : Int) + d841 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1014 p = 1 := by simpa only [d73, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2517 p hg
    simpa only [d73, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1014 p = 1 := by simpa only [d73, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2513 p hg
    simpa only [d73, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
