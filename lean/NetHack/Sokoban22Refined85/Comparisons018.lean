/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2520 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (4 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2518 p hg
    simpa only [d58, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2519 p hg
    simpa only [d58, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2521 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (4 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2520 p hg
    simpa only [d59, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d59, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2522 (p : Pattern) (guard : d1 p = 1) : d520 p ≤ (4 : Int) + d37 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d520, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2512 p hg
    simpa only [d520, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d520, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2521 p hg
    simpa only [d520, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2523 (p : Pattern) (guard : d1 p = 1) : d521 p ≤ (4 : Int) + d38 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d521, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2517 p hg
    simpa only [d521, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d521, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2522 p hg
    simpa only [d521, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2524 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d11 p := by
  change (12 : Int) ≤ (4 : Int) + 11
  decide
theorem compare2525 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2524 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2526 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2524 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2525 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2527 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2526 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2528 (p : Pattern) (guard : d1 p = 1) : d522 p ≤ (4 : Int) + d42 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d522, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2512 p hg
    simpa only [d522, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d522, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2527 p hg
    simpa only [d522, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2529 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (4 : Int) + d18 p := by
  omega
theorem compare2530 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (4 : Int) + d4 p := by
  change (8 : Int) ≤ (4 : Int) + 4
  decide
theorem compare2531 (p : Pattern) (guard : d1 p = 1) : d190 p ≤ (4 : Int) + d17 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d190, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d190, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d190, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d190, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2532 (p : Pattern) (guard : d1 p = 1) : d191 p ≤ (4 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d191, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d191, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d191, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2531 p hg
    simpa only [d191, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2533 (p : Pattern) (guard : d1 p = 1) : d523 p ≤ (4 : Int) + d18 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2529 p hg
    simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2532 p hg
    simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2534 (p : Pattern) (guard : d1 p = 1) : d524 p ≤ (4 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d524, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2533 p hg
    simpa only [d524, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d524, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d524, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2535 (p : Pattern) (guard : d1 p = 1) : d525 p ≤ (4 : Int) + d44 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d525, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d525, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d525, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2534 p hg
    simpa only [d525, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2536 (p : Pattern) (guard : d1 p = 1) : d526 p ≤ (4 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d526, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2523 p hg
    simpa only [d526, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d526, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2535 p hg
    simpa only [d526, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2537 (p : Pattern) (guard : d1 p = 1) : d522 p ≤ (4 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d522, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2512 p hg
    simpa only [d522, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d522, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d522, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2538 (p : Pattern) (guard : d1 p = 1) : d525 p ≤ (4 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d525, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2537 p hg
    simpa only [d525, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d525, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2534 p hg
    simpa only [d525, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2539 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (4 : Int) + d24 p := by
  omega
theorem compare2540 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d9 p := by
  change (12 : Int) ≤ (4 : Int) + 9
  decide
theorem compare2541 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2540 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2542 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2540 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2541 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2543 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (4 : Int) + d24 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2539 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2542 p hg
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2544 (p : Pattern) (guard : d1 p = 1) : d527 p ≤ (4 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d527, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2543 p hg
    simpa only [d527, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d527, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d527, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2545 (p : Pattern) (guard : d1 p = 1) : d528 p ≤ (4 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d528, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2544 p hg
    simpa only [d528, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d528, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d528, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2546 (p : Pattern) (guard : d1 p = 1) : d529 p ≤ (4 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d529, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2538 p hg
    simpa only [d529, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d529, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2545 p hg
    simpa only [d529, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2547 (p : Pattern) (guard : d1 p = 1) : d530 p ≤ (4 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d530, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2536 p hg
    simpa only [d530, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d530, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2546 p hg
    simpa only [d530, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2548 (p : Pattern) (guard : d1 p = 1) : d531 p ≤ (4 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d531, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2506 p hg
    simpa only [d531, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d531, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2547 p hg
    simpa only [d531, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2549 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (4 : Int) + d65 p := by
  omega
theorem compare2550 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (4 : Int) + d31 p := by
  omega
theorem compare2551 (p : Pattern) (guard : d1 p = 1) : d532 p ≤ (4 : Int) + d31 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2550 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2515 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2552 (p : Pattern) (guard : d1 p = 1) : d533 p ≤ (4 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d533, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2551 p hg
    simpa only [d533, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d533, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d533, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2553 (p : Pattern) (guard : d1 p = 1) : d534 p ≤ (4 : Int) + d67 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d534, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2522 p hg
    simpa only [d534, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d534, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2552 p hg
    simpa only [d534, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2554 (p : Pattern) (guard : d1 p = 1) : d535 p ≤ (4 : Int) + d68 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d535, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2534 p hg
    simpa only [d535, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d535, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2544 p hg
    simpa only [d535, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2555 (p : Pattern) (guard : d1 p = 1) : d536 p ≤ (4 : Int) + d69 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d536, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2553 p hg
    simpa only [d536, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d536, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2554 p hg
    simpa only [d536, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2556 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (4 : Int) + d58 p := by
  omega
theorem compare2557 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d10 p := by
  change (12 : Int) ≤ (4 : Int) + 10
  decide
theorem compare2558 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2557 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2559 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d58 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2557 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2558 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2560 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (4 : Int) + d58 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2556 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2559 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2561 (p : Pattern) (guard : d1 p = 1) : d277 p ≤ (4 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d277, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2560 p hg
    simpa only [d277, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d277, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d277, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2562 (p : Pattern) (guard : d1 p = 1) : d537 p ≤ (4 : Int) + d71 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d537, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2534 p hg
    simpa only [d537, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d537, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2561 p hg
    simpa only [d537, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2563 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (4 : Int) + d40 p := by
  omega
theorem compare2564 (p : Pattern) (guard : d1 p = 1) : d41 p ≤ (4 : Int) + d40 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2563 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2526 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2565 (p : Pattern) (guard : d1 p = 1) : d538 p ≤ (4 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d538, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2564 p hg
    simpa only [d538, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d538, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d538, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2566 (p : Pattern) (guard : d1 p = 1) : d539 p ≤ (4 : Int) + d73 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d539, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2565 p hg
    simpa only [d539, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d539, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d539, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2567 (p : Pattern) (guard : d1 p = 1) : d540 p ≤ (4 : Int) + d74 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d540, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2562 p hg
    simpa only [d540, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d540, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2566 p hg
    simpa only [d540, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2568 (p : Pattern) (guard : d1 p = 1) : d541 p ≤ (4 : Int) + d75 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d541, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2555 p hg
    simpa only [d541, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d541, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2567 p hg
    simpa only [d541, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2569 (p : Pattern) (guard : d1 p = 1) : d542 p ≤ (4 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d542, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2549 p hg
    simpa only [d542, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d542, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2568 p hg
    simpa only [d542, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2570 (p : Pattern) (guard : d1 p = 1) : d543 p ≤ (4 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d543, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2548 p hg
    simpa only [d543, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d543, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2569 p hg
    simpa only [d543, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2571 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (4 : Int) + d87 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2572 (p : Pattern) (guard : d4068 p = 1) : d544 p ≤ (4 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d544, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2570 p hg
    simpa only [d4068, d544, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d544, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2571 p hg
    simpa only [d4068, d544, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2573 (p : Pattern) (guard : d4069 p = 1) : d545 p ≤ (4 : Int) + d88 p := by
  cases selected : p 116 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4069, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2505 p hg
    simpa only [d4069, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4068 p = 1 := by simpa only [d4069, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2572 p hg
    simpa only [d4069, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2574 (p : Pattern) (guard : d0 p = 1) : d546 p ≤ (4 : Int) + d88 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2575 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d87 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2576 (p : Pattern) (guard : d4068 p = 1) : d547 p ≤ (4 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d547, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2570 p hg
    simpa only [d4068, d547, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d547, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2575 p hg
    simpa only [d4068, d547, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2577 (p : Pattern) (guard : d4069 p = 1) : d548 p ≤ (4 : Int) + d88 p := by
  cases selected : p 116 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4069, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2574 p hg
    simpa only [d4069, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4068 p = 1 := by simpa only [d4069, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2576 p hg
    simpa only [d4069, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2578 (p : Pattern) (guard : d4069 p = 1) : d549 p ≤ (4 : Int) + d88 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2573 p hg
    simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2577 p hg
    simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2579 (p : Pattern) (guard : d0 p = 1) : d550 p ≤ (4 : Int) + d88 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2580 (p : Pattern) (guard : d0 p = 1) : d441 p ≤ (4 : Int) + d87 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2581 (p : Pattern) (guard : d4068 p = 1) : d551 p ≤ (4 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d551, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2570 p hg
    simpa only [d4068, d551, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d551, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2580 p hg
    simpa only [d4068, d551, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2582 (p : Pattern) (guard : d4069 p = 1) : d552 p ≤ (4 : Int) + d88 p := by
  cases selected : p 116 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4069, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2579 p hg
    simpa only [d4069, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4068 p = 1 := by simpa only [d4069, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2581 p hg
    simpa only [d4069, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2583 (p : Pattern) (guard : d0 p = 1) : d553 p ≤ (4 : Int) + d88 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2584 (p : Pattern) (guard : d4069 p = 1) : d554 p ≤ (4 : Int) + d88 p := by
  cases selected : p 116 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4069, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2583 p hg
    simpa only [d4069, d554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4068 p = 1 := by simpa only [d4069, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2576 p hg
    simpa only [d4069, d554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2585 (p : Pattern) (guard : d4069 p = 1) : d555 p ≤ (4 : Int) + d88 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2582 p hg
    simpa only [d555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2584 p hg
    simpa only [d555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2586 (p : Pattern) (guard : d4069 p = 1) : d556 p ≤ (4 : Int) + d88 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2578 p hg
    simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2585 p hg
    simpa only [d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2587 (p : Pattern) (guard : d0 p = 1) : d557 p ≤ (4 : Int) + d158 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2588 (p : Pattern) (guard : d1 p = 1) : d114 p ≤ (4 : Int) + d114 p := by
  omega
theorem compare2589 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (4 : Int) + d103 p := by
  omega
theorem compare2590 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (4 : Int) + d1 p := by
  change (5 : Int) ≤ (4 : Int) + 1
  decide
theorem compare2591 (p : Pattern) (guard : d1 p = 1) : d106 p ≤ (4 : Int) + d102 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2590 p hg
    simpa only [d106, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d106, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2592 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (4 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d107, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2590 p hg
    simpa only [d107, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d107, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2591 p hg
    simpa only [d107, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2593 (p : Pattern) (guard : d1 p = 1) : d558 p ≤ (4 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2589 p hg
    simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2592 p hg
    simpa only [d558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2594 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (4 : Int) + d3 p := by
  change (7 : Int) ≤ (4 : Int) + 3
  decide
theorem compare2595 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (4 : Int) + d115 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2594 p hg
    simpa only [d119, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d119, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2596 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (4 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2594 p hg
    simpa only [d120, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2595 p hg
    simpa only [d120, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2597 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (4 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2596 p hg
    simpa only [d121, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d121, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2598 (p : Pattern) (guard : d1 p = 1) : d559 p ≤ (4 : Int) + d118 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d559, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2593 p hg
    simpa only [d559, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d559, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2597 p hg
    simpa only [d559, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2599 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (4 : Int) + d7 p := by
  change (11 : Int) ≤ (4 : Int) + 7
  decide
theorem compare2600 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (4 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2599 p hg
    simpa only [d39, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d39, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2601 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (4 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2599 p hg
    simpa only [d40, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2600 p hg
    simpa only [d40, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2602 (p : Pattern) (guard : d1 p = 1) : d41 p ≤ (4 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2601 p hg
    simpa only [d41, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d41, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2603 (p : Pattern) (guard : d1 p = 1) : d560 p ≤ (4 : Int) + d122 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d560, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2593 p hg
    simpa only [d560, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d560, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2602 p hg
    simpa only [d560, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2604 (p : Pattern) (guard : d1 p = 1) : d561 p ≤ (4 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d561, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2598 p hg
    simpa only [d561, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d561, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2603 p hg
    simpa only [d561, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2605 (p : Pattern) (guard : d1 p = 1) : d562 p ≤ (4 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d562, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2593 p hg
    simpa only [d562, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d562, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d562, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2606 (p : Pattern) (guard : d1 p = 1) : d107 p ≤ (4 : Int) + d107 p := by
  omega
theorem compare2607 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (4 : Int) + d5 p := by
  change (9 : Int) ≤ (4 : Int) + 5
  decide
theorem compare2608 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (4 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2607 p hg
    simpa only [d23, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d23, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2609 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (4 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2607 p hg
    simpa only [d24, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2608 p hg
    simpa only [d24, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2610 (p : Pattern) (guard : d1 p = 1) : d563 p ≤ (4 : Int) + d107 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2606 p hg
    simpa only [d563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2609 p hg
    simpa only [d563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2611 (p : Pattern) (guard : d1 p = 1) : d564 p ≤ (4 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d564, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2610 p hg
    simpa only [d564, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d564, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d564, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2612 (p : Pattern) (guard : d1 p = 1) : d565 p ≤ (4 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d565, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2605 p hg
    simpa only [d565, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d565, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2611 p hg
    simpa only [d565, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2613 (p : Pattern) (guard : d1 p = 1) : d566 p ≤ (4 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d566, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2604 p hg
    simpa only [d566, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d566, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2612 p hg
    simpa only [d566, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2614 (p : Pattern) (guard : d1 p = 1) : d278 p ≤ (4 : Int) + d128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d278, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2561 p hg
    simpa only [d278, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d278, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d278, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2615 (p : Pattern) (guard : d1 p = 1) : d567 p ≤ (4 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d567, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2612 p hg
    simpa only [d567, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d567, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2614 p hg
    simpa only [d567, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2616 (p : Pattern) (guard : d1 p = 1) : d568 p ≤ (4 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d568, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2613 p hg
    simpa only [d568, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d568, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2615 p hg
    simpa only [d568, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2617 (p : Pattern) (guard : d1 p = 1) : d569 p ≤ (4 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d569, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2588 p hg
    simpa only [d569, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d569, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2616 p hg
    simpa only [d569, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2618 (p : Pattern) (guard : d1 p = 1) : d138 p ≤ (4 : Int) + d138 p := by
  omega
theorem compare2619 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (4 : Int) + d116 p := by
  omega
theorem compare2620 (p : Pattern) (guard : d1 p = 1) : d570 p ≤ (4 : Int) + d116 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2619 p hg
    simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2596 p hg
    simpa only [d570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2621 (p : Pattern) (guard : d1 p = 1) : d571 p ≤ (4 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d571, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2620 p hg
    simpa only [d571, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d571, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d571, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2622 (p : Pattern) (guard : d1 p = 1) : d572 p ≤ (4 : Int) + d140 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d572, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2603 p hg
    simpa only [d572, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d572, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2621 p hg
    simpa only [d572, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2623 (p : Pattern) (guard : d1 p = 1) : d573 p ≤ (4 : Int) + d141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d573, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2611 p hg
    simpa only [d573, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d573, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2561 p hg
    simpa only [d573, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2624 (p : Pattern) (guard : d1 p = 1) : d574 p ≤ (4 : Int) + d142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d574, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2622 p hg
    simpa only [d574, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d574, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2623 p hg
    simpa only [d574, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2625 (p : Pattern) (guard : d1 p = 1) : d575 p ≤ (4 : Int) + d143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d575, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2611 p hg
    simpa only [d575, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d575, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2565 p hg
    simpa only [d575, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2626 (p : Pattern) (guard : d1 p = 1) : d576 p ≤ (4 : Int) + d144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d576, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2625 p hg
    simpa only [d576, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d576, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d576, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2627 (p : Pattern) (guard : d1 p = 1) : d577 p ≤ (4 : Int) + d145 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d577, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2624 p hg
    simpa only [d577, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d577, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2626 p hg
    simpa only [d577, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2628 (p : Pattern) (guard : d1 p = 1) : d578 p ≤ (4 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d578, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2618 p hg
    simpa only [d578, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d578, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2627 p hg
    simpa only [d578, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2629 (p : Pattern) (guard : d1 p = 1) : d579 p ≤ (4 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d579, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2617 p hg
    simpa only [d579, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d579, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2628 p hg
    simpa only [d579, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2630 (p : Pattern) (guard : d0 p = 1) : d441 p ≤ (4 : Int) + d157 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2631 (p : Pattern) (guard : d4068 p = 1) : d580 p ≤ (4 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d580, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2629 p hg
    simpa only [d4068, d580, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d580, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2630 p hg
    simpa only [d4068, d580, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2632 (p : Pattern) (guard : d4069 p = 1) : d581 p ≤ (4 : Int) + d158 p := by
  cases selected : p 116 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4069, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2587 p hg
    simpa only [d4069, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4068 p = 1 := by simpa only [d4069, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2631 p hg
    simpa only [d4069, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2633 (p : Pattern) (guard : d0 p = 1) : d582 p ≤ (4 : Int) + d158 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2634 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d157 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2635 (p : Pattern) (guard : d4068 p = 1) : d583 p ≤ (4 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d583, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2629 p hg
    simpa only [d4068, d583, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d583, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2634 p hg
    simpa only [d4068, d583, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2636 (p : Pattern) (guard : d4069 p = 1) : d584 p ≤ (4 : Int) + d158 p := by
  cases selected : p 116 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4069, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2633 p hg
    simpa only [d4069, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4068 p = 1 := by simpa only [d4069, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2635 p hg
    simpa only [d4069, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2637 (p : Pattern) (guard : d4069 p = 1) : d585 p ≤ (4 : Int) + d158 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2632 p hg
    simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2636 p hg
    simpa only [d585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2638 (p : Pattern) (guard : d4069 p = 1) : d586 p ≤ (4 : Int) + d4197 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d586, d4197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2578 p hg
    simpa only [d586, d4197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d586, d4197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2637 p hg
    simpa only [d586, d4197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2639 (p : Pattern) (guard : d4069 p = 1) : d587 p ≤ (4 : Int) + d4198 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d587, d4198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2586 p hg
    simpa only [d587, d4198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d587, d4198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2638 p hg
    simpa only [d587, d4198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2640 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (4 : Int) + d16 p := by
  omega
theorem compare2641 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (4 : Int) + d0 p := by
  change (2 : Int) ≤ (4 : Int) + 0
  decide
theorem compare2642 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (4 : Int) + d13 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2641 p hg
    simpa only [d30, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d30, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2643 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (4 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2641 p hg
    simpa only [d31, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2642 p hg
    simpa only [d31, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2644 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (4 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2643 p hg
    simpa only [d32, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d32, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2645 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (4 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2643 p hg
    simpa only [d53, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2644 p hg
    simpa only [d53, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2646 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (4 : Int) + d4 p := by
  change (6 : Int) ≤ (4 : Int) + 4
  decide
theorem compare2647 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (4 : Int) + d17 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2646 p hg
    simpa only [d34, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d34, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2648 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (4 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2646 p hg
    simpa only [d35, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2647 p hg
    simpa only [d35, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2649 (p : Pattern) (guard : d1 p = 1) : d36 p ≤ (4 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2648 p hg
    simpa only [d36, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d36, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2650 (p : Pattern) (guard : d1 p = 1) : d78 p ≤ (4 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d78, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2648 p hg
    simpa only [d78, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d78, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2649 p hg
    simpa only [d78, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2651 (p : Pattern) (guard : d1 p = 1) : d79 p ≤ (4 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d79, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2645 p hg
    simpa only [d79, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d79, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2650 p hg
    simpa only [d79, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2652 (p : Pattern) (guard : d1 p = 1) : d188 p ≤ (4 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d188, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2640 p hg
    simpa only [d188, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d188, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2651 p hg
    simpa only [d188, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2653 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (4 : Int) + d9 p := by
  change (11 : Int) ≤ (4 : Int) + 9
  decide
theorem compare2654 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (4 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2653 p hg
    simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d39, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2655 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (4 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2653 p hg
    simpa only [d40, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2654 p hg
    simpa only [d40, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2656 (p : Pattern) (guard : d1 p = 1) : d41 p ≤ (4 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2655 p hg
    simpa only [d41, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d41, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2657 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (4 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2655 p hg
    simpa only [d62, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2656 p hg
    simpa only [d62, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2658 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (4 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2657 p hg
    simpa only [d63, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d63, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2659 (p : Pattern) (guard : d1 p = 1) : d80 p ≤ (4 : Int) + d28 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d80, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2651 p hg
    simpa only [d80, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d80, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2658 p hg
    simpa only [d80, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
