/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes20
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d2520 (p : Pattern) : Int := if p 225 then d12 p else d18 p
theorem agree2520 (p q : Pattern) (h : Agree support p q) : d2520 p = d2520 q := by
  simp only [d2520, h 225 (by decide), agree12 p q h, agree18 p q h]
theorem nonnegative2520 (p : Pattern) : 0 ≤ d2520 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative18 p)
def d2521 (p : Pattern) : Int := if p 225 then d12 p else d1795 p
theorem agree2521 (p q : Pattern) (h : Agree support p q) : d2521 p = d2521 q := by
  simp only [d2521, h 225 (by decide), agree12 p q h, agree1795 p q h]
theorem nonnegative2521 (p : Pattern) : 0 ≤ d2521 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative1795 p)
def d2522 (p : Pattern) : Int := if p 224 then d2521 p else d2520 p
theorem agree2522 (p q : Pattern) (h : Agree support p q) : d2522 p = d2522 q := by
  simp only [d2522, h 224 (by decide), agree2521 p q h, agree2520 p q h]
theorem nonnegative2522 (p : Pattern) : 0 ≤ d2522 p :=
  nonnegative_ite (p 224) (nonnegative2521 p) (nonnegative2520 p)
def d2523 (p : Pattern) : Int := if p 204 then d2522 p else d2520 p
theorem agree2523 (p q : Pattern) (h : Agree support p q) : d2523 p = d2523 q := by
  simp only [d2523, h 204 (by decide), agree2522 p q h, agree2520 p q h]
theorem nonnegative2523 (p : Pattern) : 0 ≤ d2523 p :=
  nonnegative_ite (p 204) (nonnegative2522 p) (nonnegative2520 p)
def d2524 (p : Pattern) : Int := if p 225 then d12 p else d1694 p
theorem agree2524 (p q : Pattern) (h : Agree support p q) : d2524 p = d2524 q := by
  simp only [d2524, h 225 (by decide), agree12 p q h, agree1694 p q h]
theorem nonnegative2524 (p : Pattern) : 0 ≤ d2524 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative1694 p)
def d2525 (p : Pattern) : Int := if p 224 then d2524 p else d2520 p
theorem agree2525 (p q : Pattern) (h : Agree support p q) : d2525 p = d2525 q := by
  simp only [d2525, h 224 (by decide), agree2524 p q h, agree2520 p q h]
theorem nonnegative2525 (p : Pattern) : 0 ≤ d2525 p :=
  nonnegative_ite (p 224) (nonnegative2524 p) (nonnegative2520 p)
def d2526 (p : Pattern) : Int := if p 204 then d12 p else d2525 p
theorem agree2526 (p q : Pattern) (h : Agree support p q) : d2526 p = d2526 q := by
  simp only [d2526, h 204 (by decide), agree12 p q h, agree2525 p q h]
theorem nonnegative2526 (p : Pattern) : 0 ≤ d2526 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2525 p)
def d2527 (p : Pattern) : Int := if p 182 then d2526 p else d2523 p
theorem agree2527 (p q : Pattern) (h : Agree support p q) : d2527 p = d2527 q := by
  simp only [d2527, h 182 (by decide), agree2526 p q h, agree2523 p q h]
theorem nonnegative2527 (p : Pattern) : 0 ≤ d2527 p :=
  nonnegative_ite (p 182) (nonnegative2526 p) (nonnegative2523 p)
def d2528 (p : Pattern) : Int := if p 163 then d2527 p else d2519 p
theorem agree2528 (p q : Pattern) (h : Agree support p q) : d2528 p = d2528 q := by
  simp only [d2528, h 163 (by decide), agree2527 p q h, agree2519 p q h]
theorem nonnegative2528 (p : Pattern) : 0 ≤ d2528 p :=
  nonnegative_ite (p 163) (nonnegative2527 p) (nonnegative2519 p)
def d2529 (p : Pattern) : Int := if p 162 then d2528 p else d2517 p
theorem agree2529 (p q : Pattern) (h : Agree support p q) : d2529 p = d2529 q := by
  simp only [d2529, h 162 (by decide), agree2528 p q h, agree2517 p q h]
theorem nonnegative2529 (p : Pattern) : 0 ≤ d2529 p :=
  nonnegative_ite (p 162) (nonnegative2528 p) (nonnegative2517 p)
def d2530 (p : Pattern) : Int := if p 225 then d12 p else d24 p
theorem agree2530 (p q : Pattern) (h : Agree support p q) : d2530 p = d2530 q := by
  simp only [d2530, h 225 (by decide), agree12 p q h, agree24 p q h]
theorem nonnegative2530 (p : Pattern) : 0 ≤ d2530 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative24 p)
def d2531 (p : Pattern) : Int := if p 224 then d357 p else d2530 p
theorem agree2531 (p q : Pattern) (h : Agree support p q) : d2531 p = d2531 q := by
  simp only [d2531, h 224 (by decide), agree357 p q h, agree2530 p q h]
theorem nonnegative2531 (p : Pattern) : 0 ≤ d2531 p :=
  nonnegative_ite (p 224) (nonnegative357 p) (nonnegative2530 p)
def d2532 (p : Pattern) : Int := if p 204 then d2531 p else d2530 p
theorem agree2532 (p q : Pattern) (h : Agree support p q) : d2532 p = d2532 q := by
  simp only [d2532, h 204 (by decide), agree2531 p q h, agree2530 p q h]
theorem nonnegative2532 (p : Pattern) : 0 ≤ d2532 p :=
  nonnegative_ite (p 204) (nonnegative2531 p) (nonnegative2530 p)
def d2533 (p : Pattern) : Int := if p 225 then d12 p else d1702 p
theorem agree2533 (p q : Pattern) (h : Agree support p q) : d2533 p = d2533 q := by
  simp only [d2533, h 225 (by decide), agree12 p q h, agree1702 p q h]
theorem nonnegative2533 (p : Pattern) : 0 ≤ d2533 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative1702 p)
def d2534 (p : Pattern) : Int := if p 224 then d2533 p else d2530 p
theorem agree2534 (p q : Pattern) (h : Agree support p q) : d2534 p = d2534 q := by
  simp only [d2534, h 224 (by decide), agree2533 p q h, agree2530 p q h]
theorem nonnegative2534 (p : Pattern) : 0 ≤ d2534 p :=
  nonnegative_ite (p 224) (nonnegative2533 p) (nonnegative2530 p)
def d2535 (p : Pattern) : Int := if p 204 then d12 p else d2534 p
theorem agree2535 (p q : Pattern) (h : Agree support p q) : d2535 p = d2535 q := by
  simp only [d2535, h 204 (by decide), agree12 p q h, agree2534 p q h]
theorem nonnegative2535 (p : Pattern) : 0 ≤ d2535 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2534 p)
def d2536 (p : Pattern) : Int := if p 182 then d2535 p else d2532 p
theorem agree2536 (p q : Pattern) (h : Agree support p q) : d2536 p = d2536 q := by
  simp only [d2536, h 182 (by decide), agree2535 p q h, agree2532 p q h]
theorem nonnegative2536 (p : Pattern) : 0 ≤ d2536 p :=
  nonnegative_ite (p 182) (nonnegative2535 p) (nonnegative2532 p)
def d2537 (p : Pattern) : Int := if p 163 then d12 p else d2536 p
theorem agree2537 (p q : Pattern) (h : Agree support p q) : d2537 p = d2537 q := by
  simp only [d2537, h 163 (by decide), agree12 p q h, agree2536 p q h]
theorem nonnegative2537 (p : Pattern) : 0 ≤ d2537 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2536 p)
def d2538 (p : Pattern) : Int := if p 162 then d2537 p else d2528 p
theorem agree2538 (p q : Pattern) (h : Agree support p q) : d2538 p = d2538 q := by
  simp only [d2538, h 162 (by decide), agree2537 p q h, agree2528 p q h]
theorem nonnegative2538 (p : Pattern) : 0 ≤ d2538 p :=
  nonnegative_ite (p 162) (nonnegative2537 p) (nonnegative2528 p)
def d2539 (p : Pattern) : Int := if p 161 then d2538 p else d2529 p
theorem agree2539 (p q : Pattern) (h : Agree support p q) : d2539 p = d2539 q := by
  simp only [d2539, h 161 (by decide), agree2538 p q h, agree2529 p q h]
theorem nonnegative2539 (p : Pattern) : 0 ≤ d2539 p :=
  nonnegative_ite (p 161) (nonnegative2538 p) (nonnegative2529 p)
def d2540 (p : Pattern) : Int := if p 225 then d12 p else d31 p
theorem agree2540 (p q : Pattern) (h : Agree support p q) : d2540 p = d2540 q := by
  simp only [d2540, h 225 (by decide), agree12 p q h, agree31 p q h]
theorem nonnegative2540 (p : Pattern) : 0 ≤ d2540 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative31 p)
def d2541 (p : Pattern) : Int := if p 225 then d12 p else d1714 p
theorem agree2541 (p q : Pattern) (h : Agree support p q) : d2541 p = d2541 q := by
  simp only [d2541, h 225 (by decide), agree12 p q h, agree1714 p q h]
theorem nonnegative2541 (p : Pattern) : 0 ≤ d2541 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative1714 p)
def d2542 (p : Pattern) : Int := if p 224 then d2541 p else d2540 p
theorem agree2542 (p q : Pattern) (h : Agree support p q) : d2542 p = d2542 q := by
  simp only [d2542, h 224 (by decide), agree2541 p q h, agree2540 p q h]
theorem nonnegative2542 (p : Pattern) : 0 ≤ d2542 p :=
  nonnegative_ite (p 224) (nonnegative2541 p) (nonnegative2540 p)
def d2543 (p : Pattern) : Int := if p 204 then d12 p else d2542 p
theorem agree2543 (p q : Pattern) (h : Agree support p q) : d2543 p = d2543 q := by
  simp only [d2543, h 204 (by decide), agree12 p q h, agree2542 p q h]
theorem nonnegative2543 (p : Pattern) : 0 ≤ d2543 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2542 p)
def d2544 (p : Pattern) : Int := if p 182 then d2543 p else d2518 p
theorem agree2544 (p q : Pattern) (h : Agree support p q) : d2544 p = d2544 q := by
  simp only [d2544, h 182 (by decide), agree2543 p q h, agree2518 p q h]
theorem nonnegative2544 (p : Pattern) : 0 ≤ d2544 p :=
  nonnegative_ite (p 182) (nonnegative2543 p) (nonnegative2518 p)
def d2545 (p : Pattern) : Int := if p 225 then d12 p else d35 p
theorem agree2545 (p q : Pattern) (h : Agree support p q) : d2545 p = d2545 q := by
  simp only [d2545, h 225 (by decide), agree12 p q h, agree35 p q h]
theorem nonnegative2545 (p : Pattern) : 0 ≤ d2545 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative35 p)
def d2546 (p : Pattern) : Int := if p 225 then d12 p else d1722 p
theorem agree2546 (p q : Pattern) (h : Agree support p q) : d2546 p = d2546 q := by
  simp only [d2546, h 225 (by decide), agree12 p q h, agree1722 p q h]
theorem nonnegative2546 (p : Pattern) : 0 ≤ d2546 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative1722 p)
def d2547 (p : Pattern) : Int := if p 224 then d2546 p else d2545 p
theorem agree2547 (p q : Pattern) (h : Agree support p q) : d2547 p = d2547 q := by
  simp only [d2547, h 224 (by decide), agree2546 p q h, agree2545 p q h]
theorem nonnegative2547 (p : Pattern) : 0 ≤ d2547 p :=
  nonnegative_ite (p 224) (nonnegative2546 p) (nonnegative2545 p)
def d2548 (p : Pattern) : Int := if p 204 then d12 p else d2547 p
theorem agree2548 (p q : Pattern) (h : Agree support p q) : d2548 p = d2548 q := by
  simp only [d2548, h 204 (by decide), agree12 p q h, agree2547 p q h]
theorem nonnegative2548 (p : Pattern) : 0 ≤ d2548 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2547 p)
def d2549 (p : Pattern) : Int := if p 182 then d2548 p else d2518 p
theorem agree2549 (p q : Pattern) (h : Agree support p q) : d2549 p = d2549 q := by
  simp only [d2549, h 182 (by decide), agree2548 p q h, agree2518 p q h]
theorem nonnegative2549 (p : Pattern) : 0 ≤ d2549 p :=
  nonnegative_ite (p 182) (nonnegative2548 p) (nonnegative2518 p)
def d2550 (p : Pattern) : Int := if p 163 then d2549 p else d2544 p
theorem agree2550 (p q : Pattern) (h : Agree support p q) : d2550 p = d2550 q := by
  simp only [d2550, h 163 (by decide), agree2549 p q h, agree2544 p q h]
theorem nonnegative2550 (p : Pattern) : 0 ≤ d2550 p :=
  nonnegative_ite (p 163) (nonnegative2549 p) (nonnegative2544 p)
def d2551 (p : Pattern) : Int := if p 225 then d12 p else d40 p
theorem agree2551 (p q : Pattern) (h : Agree support p q) : d2551 p = d2551 q := by
  simp only [d2551, h 225 (by decide), agree12 p q h, agree40 p q h]
theorem nonnegative2551 (p : Pattern) : 0 ≤ d2551 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative40 p)
def d2552 (p : Pattern) : Int := if p 224 then d332 p else d2551 p
theorem agree2552 (p q : Pattern) (h : Agree support p q) : d2552 p = d2552 q := by
  simp only [d2552, h 224 (by decide), agree332 p q h, agree2551 p q h]
theorem nonnegative2552 (p : Pattern) : 0 ≤ d2552 p :=
  nonnegative_ite (p 224) (nonnegative332 p) (nonnegative2551 p)
def d2553 (p : Pattern) : Int := if p 204 then d12 p else d2552 p
theorem agree2553 (p q : Pattern) (h : Agree support p q) : d2553 p = d2553 q := by
  simp only [d2553, h 204 (by decide), agree12 p q h, agree2552 p q h]
theorem nonnegative2553 (p : Pattern) : 0 ≤ d2553 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2552 p)
def d2554 (p : Pattern) : Int := if p 182 then d2553 p else d2518 p
theorem agree2554 (p q : Pattern) (h : Agree support p q) : d2554 p = d2554 q := by
  simp only [d2554, h 182 (by decide), agree2553 p q h, agree2518 p q h]
theorem nonnegative2554 (p : Pattern) : 0 ≤ d2554 p :=
  nonnegative_ite (p 182) (nonnegative2553 p) (nonnegative2518 p)
def d2555 (p : Pattern) : Int := if p 182 then d12 p else d2523 p
theorem agree2555 (p q : Pattern) (h : Agree support p q) : d2555 p = d2555 q := by
  simp only [d2555, h 182 (by decide), agree12 p q h, agree2523 p q h]
theorem nonnegative2555 (p : Pattern) : 0 ≤ d2555 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2523 p)
def d2556 (p : Pattern) : Int := if p 163 then d2555 p else d2554 p
theorem agree2556 (p q : Pattern) (h : Agree support p q) : d2556 p = d2556 q := by
  simp only [d2556, h 163 (by decide), agree2555 p q h, agree2554 p q h]
theorem nonnegative2556 (p : Pattern) : 0 ≤ d2556 p :=
  nonnegative_ite (p 163) (nonnegative2555 p) (nonnegative2554 p)
def d2557 (p : Pattern) : Int := if p 162 then d2556 p else d2550 p
theorem agree2557 (p q : Pattern) (h : Agree support p q) : d2557 p = d2557 q := by
  simp only [d2557, h 162 (by decide), agree2556 p q h, agree2550 p q h]
theorem nonnegative2557 (p : Pattern) : 0 ≤ d2557 p :=
  nonnegative_ite (p 162) (nonnegative2556 p) (nonnegative2550 p)
def d2558 (p : Pattern) : Int := if p 182 then d12 p else d2518 p
theorem agree2558 (p q : Pattern) (h : Agree support p q) : d2558 p = d2558 q := by
  simp only [d2558, h 182 (by decide), agree12 p q h, agree2518 p q h]
theorem nonnegative2558 (p : Pattern) : 0 ≤ d2558 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2518 p)
def d2559 (p : Pattern) : Int := if p 163 then d2555 p else d2558 p
theorem agree2559 (p q : Pattern) (h : Agree support p q) : d2559 p = d2559 q := by
  simp only [d2559, h 163 (by decide), agree2555 p q h, agree2558 p q h]
theorem nonnegative2559 (p : Pattern) : 0 ≤ d2559 p :=
  nonnegative_ite (p 163) (nonnegative2555 p) (nonnegative2558 p)
def d2560 (p : Pattern) : Int := if p 182 then d12 p else d2532 p
theorem agree2560 (p q : Pattern) (h : Agree support p q) : d2560 p = d2560 q := by
  simp only [d2560, h 182 (by decide), agree12 p q h, agree2532 p q h]
theorem nonnegative2560 (p : Pattern) : 0 ≤ d2560 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2532 p)
def d2561 (p : Pattern) : Int := if p 163 then d12 p else d2560 p
theorem agree2561 (p q : Pattern) (h : Agree support p q) : d2561 p = d2561 q := by
  simp only [d2561, h 163 (by decide), agree12 p q h, agree2560 p q h]
theorem nonnegative2561 (p : Pattern) : 0 ≤ d2561 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2560 p)
def d2562 (p : Pattern) : Int := if p 162 then d2561 p else d2559 p
theorem agree2562 (p q : Pattern) (h : Agree support p q) : d2562 p = d2562 q := by
  simp only [d2562, h 162 (by decide), agree2561 p q h, agree2559 p q h]
theorem nonnegative2562 (p : Pattern) : 0 ≤ d2562 p :=
  nonnegative_ite (p 162) (nonnegative2561 p) (nonnegative2559 p)
def d2563 (p : Pattern) : Int := if p 161 then d2562 p else d2557 p
theorem agree2563 (p q : Pattern) (h : Agree support p q) : d2563 p = d2563 q := by
  simp only [d2563, h 161 (by decide), agree2562 p q h, agree2557 p q h]
theorem nonnegative2563 (p : Pattern) : 0 ≤ d2563 p :=
  nonnegative_ite (p 161) (nonnegative2562 p) (nonnegative2557 p)
def d2564 (p : Pattern) : Int := if p 160 then d2563 p else d2539 p
theorem agree2564 (p q : Pattern) (h : Agree support p q) : d2564 p = d2564 q := by
  simp only [d2564, h 160 (by decide), agree2563 p q h, agree2539 p q h]
theorem nonnegative2564 (p : Pattern) : 0 ≤ d2564 p :=
  nonnegative_ite (p 160) (nonnegative2563 p) (nonnegative2539 p)
def d2565 (p : Pattern) : Int := if p 225 then d329 p else d14 p
theorem agree2565 (p q : Pattern) (h : Agree support p q) : d2565 p = d2565 q := by
  simp only [d2565, h 225 (by decide), agree329 p q h, agree14 p q h]
theorem nonnegative2565 (p : Pattern) : 0 ≤ d2565 p :=
  nonnegative_ite (p 225) (nonnegative329 p) (nonnegative14 p)
def d2566 (p : Pattern) : Int := if p 224 then d2504 p else d2565 p
theorem agree2566 (p q : Pattern) (h : Agree support p q) : d2566 p = d2566 q := by
  simp only [d2566, h 224 (by decide), agree2504 p q h, agree2565 p q h]
theorem nonnegative2566 (p : Pattern) : 0 ≤ d2566 p :=
  nonnegative_ite (p 224) (nonnegative2504 p) (nonnegative2565 p)
def d2567 (p : Pattern) : Int := if p 204 then d2507 p else d2566 p
theorem agree2567 (p q : Pattern) (h : Agree support p q) : d2567 p = d2567 q := by
  simp only [d2567, h 204 (by decide), agree2507 p q h, agree2566 p q h]
theorem nonnegative2567 (p : Pattern) : 0 ≤ d2567 p :=
  nonnegative_ite (p 204) (nonnegative2507 p) (nonnegative2566 p)
def d2568 (p : Pattern) : Int := if p 182 then d2511 p else d2567 p
theorem agree2568 (p q : Pattern) (h : Agree support p q) : d2568 p = d2568 q := by
  simp only [d2568, h 182 (by decide), agree2511 p q h, agree2567 p q h]
theorem nonnegative2568 (p : Pattern) : 0 ≤ d2568 p :=
  nonnegative_ite (p 182) (nonnegative2511 p) (nonnegative2567 p)
def d2569 (p : Pattern) : Int := if p 204 then d2542 p else d2540 p
theorem agree2569 (p q : Pattern) (h : Agree support p q) : d2569 p = d2569 q := by
  simp only [d2569, h 204 (by decide), agree2542 p q h, agree2540 p q h]
theorem nonnegative2569 (p : Pattern) : 0 ≤ d2569 p :=
  nonnegative_ite (p 204) (nonnegative2542 p) (nonnegative2540 p)
def d2570 (p : Pattern) : Int := if p 225 then d12 p else d1743 p
theorem agree2570 (p q : Pattern) (h : Agree support p q) : d2570 p = d2570 q := by
  simp only [d2570, h 225 (by decide), agree12 p q h, agree1743 p q h]
theorem nonnegative2570 (p : Pattern) : 0 ≤ d2570 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative1743 p)
def d2571 (p : Pattern) : Int := if p 224 then d2570 p else d2540 p
theorem agree2571 (p q : Pattern) (h : Agree support p q) : d2571 p = d2571 q := by
  simp only [d2571, h 224 (by decide), agree2570 p q h, agree2540 p q h]
theorem nonnegative2571 (p : Pattern) : 0 ≤ d2571 p :=
  nonnegative_ite (p 224) (nonnegative2570 p) (nonnegative2540 p)
def d2572 (p : Pattern) : Int := if p 204 then d12 p else d2571 p
theorem agree2572 (p q : Pattern) (h : Agree support p q) : d2572 p = d2572 q := by
  simp only [d2572, h 204 (by decide), agree12 p q h, agree2571 p q h]
theorem nonnegative2572 (p : Pattern) : 0 ≤ d2572 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2571 p)
def d2573 (p : Pattern) : Int := if p 182 then d2572 p else d2569 p
theorem agree2573 (p q : Pattern) (h : Agree support p q) : d2573 p = d2573 q := by
  simp only [d2573, h 182 (by decide), agree2572 p q h, agree2569 p q h]
theorem nonnegative2573 (p : Pattern) : 0 ≤ d2573 p :=
  nonnegative_ite (p 182) (nonnegative2572 p) (nonnegative2569 p)
def d2574 (p : Pattern) : Int := if p 163 then d2573 p else d2568 p
theorem agree2574 (p q : Pattern) (h : Agree support p q) : d2574 p = d2574 q := by
  simp only [d2574, h 163 (by decide), agree2573 p q h, agree2568 p q h]
theorem nonnegative2574 (p : Pattern) : 0 ≤ d2574 p :=
  nonnegative_ite (p 163) (nonnegative2573 p) (nonnegative2568 p)
def d2575 (p : Pattern) : Int := if p 163 then d2536 p else d2527 p
theorem agree2575 (p q : Pattern) (h : Agree support p q) : d2575 p = d2575 q := by
  simp only [d2575, h 163 (by decide), agree2536 p q h, agree2527 p q h]
theorem nonnegative2575 (p : Pattern) : 0 ≤ d2575 p :=
  nonnegative_ite (p 163) (nonnegative2536 p) (nonnegative2527 p)
def d2576 (p : Pattern) : Int := if p 162 then d2575 p else d2574 p
theorem agree2576 (p q : Pattern) (h : Agree support p q) : d2576 p = d2576 q := by
  simp only [d2576, h 162 (by decide), agree2575 p q h, agree2574 p q h]
theorem nonnegative2576 (p : Pattern) : 0 ≤ d2576 p :=
  nonnegative_ite (p 162) (nonnegative2575 p) (nonnegative2574 p)
def d2577 (p : Pattern) : Int := if p 225 then d12 p else d58 p
theorem agree2577 (p q : Pattern) (h : Agree support p q) : d2577 p = d2577 q := by
  simp only [d2577, h 225 (by decide), agree12 p q h, agree58 p q h]
theorem nonnegative2577 (p : Pattern) : 0 ≤ d2577 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative58 p)
def d2578 (p : Pattern) : Int := if p 224 then d330 p else d2577 p
theorem agree2578 (p q : Pattern) (h : Agree support p q) : d2578 p = d2578 q := by
  simp only [d2578, h 224 (by decide), agree330 p q h, agree2577 p q h]
theorem nonnegative2578 (p : Pattern) : 0 ≤ d2578 p :=
  nonnegative_ite (p 224) (nonnegative330 p) (nonnegative2577 p)
def d2579 (p : Pattern) : Int := if p 204 then d2578 p else d2577 p
theorem agree2579 (p q : Pattern) (h : Agree support p q) : d2579 p = d2579 q := by
  simp only [d2579, h 204 (by decide), agree2578 p q h, agree2577 p q h]
theorem nonnegative2579 (p : Pattern) : 0 ≤ d2579 p :=
  nonnegative_ite (p 204) (nonnegative2578 p) (nonnegative2577 p)
def d2580 (p : Pattern) : Int := if p 204 then d12 p else d2578 p
theorem agree2580 (p q : Pattern) (h : Agree support p q) : d2580 p = d2580 q := by
  simp only [d2580, h 204 (by decide), agree12 p q h, agree2578 p q h]
theorem nonnegative2580 (p : Pattern) : 0 ≤ d2580 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2578 p)
def d2581 (p : Pattern) : Int := if p 182 then d2580 p else d2579 p
theorem agree2581 (p q : Pattern) (h : Agree support p q) : d2581 p = d2581 q := by
  simp only [d2581, h 182 (by decide), agree2580 p q h, agree2579 p q h]
theorem nonnegative2581 (p : Pattern) : 0 ≤ d2581 p :=
  nonnegative_ite (p 182) (nonnegative2580 p) (nonnegative2579 p)
def d2582 (p : Pattern) : Int := if p 163 then d2581 p else d2527 p
theorem agree2582 (p q : Pattern) (h : Agree support p q) : d2582 p = d2582 q := by
  simp only [d2582, h 163 (by decide), agree2581 p q h, agree2527 p q h]
theorem nonnegative2582 (p : Pattern) : 0 ≤ d2582 p :=
  nonnegative_ite (p 163) (nonnegative2581 p) (nonnegative2527 p)
def d2583 (p : Pattern) : Int := if p 204 then d2552 p else d2551 p
theorem agree2583 (p q : Pattern) (h : Agree support p q) : d2583 p = d2583 q := by
  simp only [d2583, h 204 (by decide), agree2552 p q h, agree2551 p q h]
theorem nonnegative2583 (p : Pattern) : 0 ≤ d2583 p :=
  nonnegative_ite (p 204) (nonnegative2552 p) (nonnegative2551 p)
def d2584 (p : Pattern) : Int := if p 182 then d2553 p else d2583 p
theorem agree2584 (p q : Pattern) (h : Agree support p q) : d2584 p = d2584 q := by
  simp only [d2584, h 182 (by decide), agree2553 p q h, agree2583 p q h]
theorem nonnegative2584 (p : Pattern) : 0 ≤ d2584 p :=
  nonnegative_ite (p 182) (nonnegative2553 p) (nonnegative2583 p)
def d2585 (p : Pattern) : Int := if p 163 then d12 p else d2584 p
theorem agree2585 (p q : Pattern) (h : Agree support p q) : d2585 p = d2585 q := by
  simp only [d2585, h 163 (by decide), agree12 p q h, agree2584 p q h]
theorem nonnegative2585 (p : Pattern) : 0 ≤ d2585 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2584 p)
def d2586 (p : Pattern) : Int := if p 162 then d2585 p else d2582 p
theorem agree2586 (p q : Pattern) (h : Agree support p q) : d2586 p = d2586 q := by
  simp only [d2586, h 162 (by decide), agree2585 p q h, agree2582 p q h]
theorem nonnegative2586 (p : Pattern) : 0 ≤ d2586 p :=
  nonnegative_ite (p 162) (nonnegative2585 p) (nonnegative2582 p)
def d2587 (p : Pattern) : Int := if p 161 then d2586 p else d2576 p
theorem agree2587 (p q : Pattern) (h : Agree support p q) : d2587 p = d2587 q := by
  simp only [d2587, h 161 (by decide), agree2586 p q h, agree2576 p q h]
theorem nonnegative2587 (p : Pattern) : 0 ≤ d2587 p :=
  nonnegative_ite (p 161) (nonnegative2586 p) (nonnegative2576 p)
def d2588 (p : Pattern) : Int := if p 182 then d12 p else d2569 p
theorem agree2588 (p q : Pattern) (h : Agree support p q) : d2588 p = d2588 q := by
  simp only [d2588, h 182 (by decide), agree12 p q h, agree2569 p q h]
theorem nonnegative2588 (p : Pattern) : 0 ≤ d2588 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2569 p)
def d2589 (p : Pattern) : Int := if p 163 then d2588 p else d2549 p
theorem agree2589 (p q : Pattern) (h : Agree support p q) : d2589 p = d2589 q := by
  simp only [d2589, h 163 (by decide), agree2588 p q h, agree2549 p q h]
theorem nonnegative2589 (p : Pattern) : 0 ≤ d2589 p :=
  nonnegative_ite (p 163) (nonnegative2588 p) (nonnegative2549 p)
def d2590 (p : Pattern) : Int := if p 163 then d2560 p else d2555 p
theorem agree2590 (p q : Pattern) (h : Agree support p q) : d2590 p = d2590 q := by
  simp only [d2590, h 163 (by decide), agree2560 p q h, agree2555 p q h]
theorem nonnegative2590 (p : Pattern) : 0 ≤ d2590 p :=
  nonnegative_ite (p 163) (nonnegative2560 p) (nonnegative2555 p)
def d2591 (p : Pattern) : Int := if p 162 then d2590 p else d2589 p
theorem agree2591 (p q : Pattern) (h : Agree support p q) : d2591 p = d2591 q := by
  simp only [d2591, h 162 (by decide), agree2590 p q h, agree2589 p q h]
theorem nonnegative2591 (p : Pattern) : 0 ≤ d2591 p :=
  nonnegative_ite (p 162) (nonnegative2590 p) (nonnegative2589 p)
def d2592 (p : Pattern) : Int := if p 182 then d12 p else d2579 p
theorem agree2592 (p q : Pattern) (h : Agree support p q) : d2592 p = d2592 q := by
  simp only [d2592, h 182 (by decide), agree12 p q h, agree2579 p q h]
theorem nonnegative2592 (p : Pattern) : 0 ≤ d2592 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2579 p)
def d2593 (p : Pattern) : Int := if p 163 then d2592 p else d2555 p
theorem agree2593 (p q : Pattern) (h : Agree support p q) : d2593 p = d2593 q := by
  simp only [d2593, h 163 (by decide), agree2592 p q h, agree2555 p q h]
theorem nonnegative2593 (p : Pattern) : 0 ≤ d2593 p :=
  nonnegative_ite (p 163) (nonnegative2592 p) (nonnegative2555 p)
def d2594 (p : Pattern) : Int := if p 182 then d12 p else d2583 p
theorem agree2594 (p q : Pattern) (h : Agree support p q) : d2594 p = d2594 q := by
  simp only [d2594, h 182 (by decide), agree12 p q h, agree2583 p q h]
theorem nonnegative2594 (p : Pattern) : 0 ≤ d2594 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2583 p)
def d2595 (p : Pattern) : Int := if p 163 then d12 p else d2594 p
theorem agree2595 (p q : Pattern) (h : Agree support p q) : d2595 p = d2595 q := by
  simp only [d2595, h 163 (by decide), agree12 p q h, agree2594 p q h]
theorem nonnegative2595 (p : Pattern) : 0 ≤ d2595 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2594 p)
def d2596 (p : Pattern) : Int := if p 162 then d2595 p else d2593 p
theorem agree2596 (p q : Pattern) (h : Agree support p q) : d2596 p = d2596 q := by
  simp only [d2596, h 162 (by decide), agree2595 p q h, agree2593 p q h]
theorem nonnegative2596 (p : Pattern) : 0 ≤ d2596 p :=
  nonnegative_ite (p 162) (nonnegative2595 p) (nonnegative2593 p)
def d2597 (p : Pattern) : Int := if p 161 then d2596 p else d2591 p
theorem agree2597 (p q : Pattern) (h : Agree support p q) : d2597 p = d2597 q := by
  simp only [d2597, h 161 (by decide), agree2596 p q h, agree2591 p q h]
theorem nonnegative2597 (p : Pattern) : 0 ≤ d2597 p :=
  nonnegative_ite (p 161) (nonnegative2596 p) (nonnegative2591 p)
def d2598 (p : Pattern) : Int := if p 160 then d2597 p else d2587 p
theorem agree2598 (p q : Pattern) (h : Agree support p q) : d2598 p = d2598 q := by
  simp only [d2598, h 160 (by decide), agree2597 p q h, agree2587 p q h]
theorem nonnegative2598 (p : Pattern) : 0 ≤ d2598 p :=
  nonnegative_ite (p 160) (nonnegative2597 p) (nonnegative2587 p)
def d2599 (p : Pattern) : Int := if p 141 then d2598 p else d2564 p
theorem agree2599 (p q : Pattern) (h : Agree support p q) : d2599 p = d2599 q := by
  simp only [d2599, h 141 (by decide), agree2598 p q h, agree2564 p q h]
theorem nonnegative2599 (p : Pattern) : 0 ≤ d2599 p :=
  nonnegative_ite (p 141) (nonnegative2598 p) (nonnegative2564 p)
def d2600 (p : Pattern) : Int := if p 204 then d12 p else d2507 p
theorem agree2600 (p q : Pattern) (h : Agree support p q) : d2600 p = d2600 q := by
  simp only [d2600, h 204 (by decide), agree12 p q h, agree2507 p q h]
theorem nonnegative2600 (p : Pattern) : 0 ≤ d2600 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2507 p)
def d2601 (p : Pattern) : Int := if p 182 then d2600 p else d2518 p
theorem agree2601 (p q : Pattern) (h : Agree support p q) : d2601 p = d2601 q := by
  simp only [d2601, h 182 (by decide), agree2600 p q h, agree2518 p q h]
theorem nonnegative2601 (p : Pattern) : 0 ≤ d2601 p :=
  nonnegative_ite (p 182) (nonnegative2600 p) (nonnegative2518 p)
def d2602 (p : Pattern) : Int := if p 204 then d12 p else d2522 p
theorem agree2602 (p q : Pattern) (h : Agree support p q) : d2602 p = d2602 q := by
  simp only [d2602, h 204 (by decide), agree12 p q h, agree2522 p q h]
theorem nonnegative2602 (p : Pattern) : 0 ≤ d2602 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2522 p)
def d2603 (p : Pattern) : Int := if p 182 then d2602 p else d2523 p
theorem agree2603 (p q : Pattern) (h : Agree support p q) : d2603 p = d2603 q := by
  simp only [d2603, h 182 (by decide), agree2602 p q h, agree2523 p q h]
theorem nonnegative2603 (p : Pattern) : 0 ≤ d2603 p :=
  nonnegative_ite (p 182) (nonnegative2602 p) (nonnegative2523 p)
def d2604 (p : Pattern) : Int := if p 163 then d2603 p else d2601 p
theorem agree2604 (p q : Pattern) (h : Agree support p q) : d2604 p = d2604 q := by
  simp only [d2604, h 163 (by decide), agree2603 p q h, agree2601 p q h]
theorem nonnegative2604 (p : Pattern) : 0 ≤ d2604 p :=
  nonnegative_ite (p 163) (nonnegative2603 p) (nonnegative2601 p)
def d2605 (p : Pattern) : Int := if p 162 then d2604 p else d2601 p
theorem agree2605 (p q : Pattern) (h : Agree support p q) : d2605 p = d2605 q := by
  simp only [d2605, h 162 (by decide), agree2604 p q h, agree2601 p q h]
theorem nonnegative2605 (p : Pattern) : 0 ≤ d2605 p :=
  nonnegative_ite (p 162) (nonnegative2604 p) (nonnegative2601 p)
def d2606 (p : Pattern) : Int := if p 204 then d12 p else d2531 p
theorem agree2606 (p q : Pattern) (h : Agree support p q) : d2606 p = d2606 q := by
  simp only [d2606, h 204 (by decide), agree12 p q h, agree2531 p q h]
theorem nonnegative2606 (p : Pattern) : 0 ≤ d2606 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2531 p)
def d2607 (p : Pattern) : Int := if p 182 then d2606 p else d2532 p
theorem agree2607 (p q : Pattern) (h : Agree support p q) : d2607 p = d2607 q := by
  simp only [d2607, h 182 (by decide), agree2606 p q h, agree2532 p q h]
theorem nonnegative2607 (p : Pattern) : 0 ≤ d2607 p :=
  nonnegative_ite (p 182) (nonnegative2606 p) (nonnegative2532 p)
def d2608 (p : Pattern) : Int := if p 163 then d12 p else d2607 p
theorem agree2608 (p q : Pattern) (h : Agree support p q) : d2608 p = d2608 q := by
  simp only [d2608, h 163 (by decide), agree12 p q h, agree2607 p q h]
theorem nonnegative2608 (p : Pattern) : 0 ≤ d2608 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2607 p)
def d2609 (p : Pattern) : Int := if p 162 then d2608 p else d2604 p
theorem agree2609 (p q : Pattern) (h : Agree support p q) : d2609 p = d2609 q := by
  simp only [d2609, h 162 (by decide), agree2608 p q h, agree2604 p q h]
theorem nonnegative2609 (p : Pattern) : 0 ≤ d2609 p :=
  nonnegative_ite (p 162) (nonnegative2608 p) (nonnegative2604 p)
def d2610 (p : Pattern) : Int := if p 161 then d2609 p else d2605 p
theorem agree2610 (p q : Pattern) (h : Agree support p q) : d2610 p = d2610 q := by
  simp only [d2610, h 161 (by decide), agree2609 p q h, agree2605 p q h]
theorem nonnegative2610 (p : Pattern) : 0 ≤ d2610 p :=
  nonnegative_ite (p 161) (nonnegative2609 p) (nonnegative2605 p)
def d2611 (p : Pattern) : Int := if p 182 then d2543 p else d2569 p
theorem agree2611 (p q : Pattern) (h : Agree support p q) : d2611 p = d2611 q := by
  simp only [d2611, h 182 (by decide), agree2543 p q h, agree2569 p q h]
theorem nonnegative2611 (p : Pattern) : 0 ≤ d2611 p :=
  nonnegative_ite (p 182) (nonnegative2543 p) (nonnegative2569 p)
def d2612 (p : Pattern) : Int := if p 204 then d2547 p else d2545 p
theorem agree2612 (p q : Pattern) (h : Agree support p q) : d2612 p = d2612 q := by
  simp only [d2612, h 204 (by decide), agree2547 p q h, agree2545 p q h]
theorem nonnegative2612 (p : Pattern) : 0 ≤ d2612 p :=
  nonnegative_ite (p 204) (nonnegative2547 p) (nonnegative2545 p)
def d2613 (p : Pattern) : Int := if p 182 then d2548 p else d2612 p
theorem agree2613 (p q : Pattern) (h : Agree support p q) : d2613 p = d2613 q := by
  simp only [d2613, h 182 (by decide), agree2548 p q h, agree2612 p q h]
theorem nonnegative2613 (p : Pattern) : 0 ≤ d2613 p :=
  nonnegative_ite (p 182) (nonnegative2548 p) (nonnegative2612 p)
def d2614 (p : Pattern) : Int := if p 163 then d2613 p else d2611 p
theorem agree2614 (p q : Pattern) (h : Agree support p q) : d2614 p = d2614 q := by
  simp only [d2614, h 163 (by decide), agree2613 p q h, agree2611 p q h]
theorem nonnegative2614 (p : Pattern) : 0 ≤ d2614 p :=
  nonnegative_ite (p 163) (nonnegative2613 p) (nonnegative2611 p)
def d2615 (p : Pattern) : Int := if p 162 then d2585 p else d2614 p
theorem agree2615 (p q : Pattern) (h : Agree support p q) : d2615 p = d2615 q := by
  simp only [d2615, h 162 (by decide), agree2585 p q h, agree2614 p q h]
theorem nonnegative2615 (p : Pattern) : 0 ≤ d2615 p :=
  nonnegative_ite (p 162) (nonnegative2585 p) (nonnegative2614 p)
def d2616 (p : Pattern) : Int := if p 161 then d12 p else d2615 p
theorem agree2616 (p q : Pattern) (h : Agree support p q) : d2616 p = d2616 q := by
  simp only [d2616, h 161 (by decide), agree12 p q h, agree2615 p q h]
theorem nonnegative2616 (p : Pattern) : 0 ≤ d2616 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2615 p)
def d2617 (p : Pattern) : Int := if p 160 then d2616 p else d2610 p
theorem agree2617 (p q : Pattern) (h : Agree support p q) : d2617 p = d2617 q := by
  simp only [d2617, h 160 (by decide), agree2616 p q h, agree2610 p q h]
theorem nonnegative2617 (p : Pattern) : 0 ≤ d2617 p :=
  nonnegative_ite (p 160) (nonnegative2616 p) (nonnegative2610 p)
def d2618 (p : Pattern) : Int := if p 163 then d2611 p else d2601 p
theorem agree2618 (p q : Pattern) (h : Agree support p q) : d2618 p = d2618 q := by
  simp only [d2618, h 163 (by decide), agree2611 p q h, agree2601 p q h]
theorem nonnegative2618 (p : Pattern) : 0 ≤ d2618 p :=
  nonnegative_ite (p 163) (nonnegative2611 p) (nonnegative2601 p)
def d2619 (p : Pattern) : Int := if p 163 then d2607 p else d2603 p
theorem agree2619 (p q : Pattern) (h : Agree support p q) : d2619 p = d2619 q := by
  simp only [d2619, h 163 (by decide), agree2607 p q h, agree2603 p q h]
theorem nonnegative2619 (p : Pattern) : 0 ≤ d2619 p :=
  nonnegative_ite (p 163) (nonnegative2607 p) (nonnegative2603 p)
def d2620 (p : Pattern) : Int := if p 162 then d2619 p else d2618 p
theorem agree2620 (p q : Pattern) (h : Agree support p q) : d2620 p = d2620 q := by
  simp only [d2620, h 162 (by decide), agree2619 p q h, agree2618 p q h]
theorem nonnegative2620 (p : Pattern) : 0 ≤ d2620 p :=
  nonnegative_ite (p 162) (nonnegative2619 p) (nonnegative2618 p)
def d2621 (p : Pattern) : Int := if p 163 then d2581 p else d2603 p
theorem agree2621 (p q : Pattern) (h : Agree support p q) : d2621 p = d2621 q := by
  simp only [d2621, h 163 (by decide), agree2581 p q h, agree2603 p q h]
theorem nonnegative2621 (p : Pattern) : 0 ≤ d2621 p :=
  nonnegative_ite (p 163) (nonnegative2581 p) (nonnegative2603 p)
def d2622 (p : Pattern) : Int := if p 162 then d2585 p else d2621 p
theorem agree2622 (p q : Pattern) (h : Agree support p q) : d2622 p = d2622 q := by
  simp only [d2622, h 162 (by decide), agree2585 p q h, agree2621 p q h]
theorem nonnegative2622 (p : Pattern) : 0 ≤ d2622 p :=
  nonnegative_ite (p 162) (nonnegative2585 p) (nonnegative2621 p)
def d2623 (p : Pattern) : Int := if p 161 then d2622 p else d2620 p
theorem agree2623 (p q : Pattern) (h : Agree support p q) : d2623 p = d2623 q := by
  simp only [d2623, h 161 (by decide), agree2622 p q h, agree2620 p q h]
theorem nonnegative2623 (p : Pattern) : 0 ≤ d2623 p :=
  nonnegative_ite (p 161) (nonnegative2622 p) (nonnegative2620 p)
def d2624 (p : Pattern) : Int := if p 163 then d12 p else d2613 p
theorem agree2624 (p q : Pattern) (h : Agree support p q) : d2624 p = d2624 q := by
  simp only [d2624, h 163 (by decide), agree12 p q h, agree2613 p q h]
theorem nonnegative2624 (p : Pattern) : 0 ≤ d2624 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2613 p)
def d2625 (p : Pattern) : Int := if p 162 then d12 p else d2624 p
theorem agree2625 (p q : Pattern) (h : Agree support p q) : d2625 p = d2625 q := by
  simp only [d2625, h 162 (by decide), agree12 p q h, agree2624 p q h]
theorem nonnegative2625 (p : Pattern) : 0 ≤ d2625 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2624 p)
def d2626 (p : Pattern) : Int := if p 161 then d12 p else d2625 p
theorem agree2626 (p q : Pattern) (h : Agree support p q) : d2626 p = d2626 q := by
  simp only [d2626, h 161 (by decide), agree12 p q h, agree2625 p q h]
theorem nonnegative2626 (p : Pattern) : 0 ≤ d2626 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2625 p)
def d2627 (p : Pattern) : Int := if p 160 then d2626 p else d2623 p
theorem agree2627 (p q : Pattern) (h : Agree support p q) : d2627 p = d2627 q := by
  simp only [d2627, h 160 (by decide), agree2626 p q h, agree2623 p q h]
theorem nonnegative2627 (p : Pattern) : 0 ≤ d2627 p :=
  nonnegative_ite (p 160) (nonnegative2626 p) (nonnegative2623 p)
def d2628 (p : Pattern) : Int := if p 141 then d2627 p else d2617 p
theorem agree2628 (p q : Pattern) (h : Agree support p q) : d2628 p = d2628 q := by
  simp only [d2628, h 141 (by decide), agree2627 p q h, agree2617 p q h]
theorem nonnegative2628 (p : Pattern) : 0 ≤ d2628 p :=
  nonnegative_ite (p 141) (nonnegative2627 p) (nonnegative2617 p)
def d2629 (p : Pattern) : Int := if p 138 then d2628 p else d2599 p
theorem agree2629 (p q : Pattern) (h : Agree support p q) : d2629 p = d2629 q := by
  simp only [d2629, h 138 (by decide), agree2628 p q h, agree2599 p q h]
theorem nonnegative2629 (p : Pattern) : 0 ≤ d2629 p :=
  nonnegative_ite (p 138) (nonnegative2628 p) (nonnegative2599 p)
def d2630 (p : Pattern) : Int := if p 163 then d2584 p else d2607 p
theorem agree2630 (p q : Pattern) (h : Agree support p q) : d2630 p = d2630 q := by
  simp only [d2630, h 163 (by decide), agree2584 p q h, agree2607 p q h]
theorem nonnegative2630 (p : Pattern) : 0 ≤ d2630 p :=
  nonnegative_ite (p 163) (nonnegative2584 p) (nonnegative2607 p)
def d2631 (p : Pattern) : Int := if p 162 then d2585 p else d2630 p
theorem agree2631 (p q : Pattern) (h : Agree support p q) : d2631 p = d2631 q := by
  simp only [d2631, h 162 (by decide), agree2585 p q h, agree2630 p q h]
theorem nonnegative2631 (p : Pattern) : 0 ≤ d2631 p :=
  nonnegative_ite (p 162) (nonnegative2585 p) (nonnegative2630 p)
def d2632 (p : Pattern) : Int := if p 162 then d12 p else d2585 p
theorem agree2632 (p q : Pattern) (h : Agree support p q) : d2632 p = d2632 q := by
  simp only [d2632, h 162 (by decide), agree12 p q h, agree2585 p q h]
theorem nonnegative2632 (p : Pattern) : 0 ≤ d2632 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2585 p)
def d2633 (p : Pattern) : Int := if p 161 then d2632 p else d2631 p
theorem agree2633 (p q : Pattern) (h : Agree support p q) : d2633 p = d2633 q := by
  simp only [d2633, h 161 (by decide), agree2632 p q h, agree2631 p q h]
theorem nonnegative2633 (p : Pattern) : 0 ≤ d2633 p :=
  nonnegative_ite (p 161) (nonnegative2632 p) (nonnegative2631 p)
def d2634 (p : Pattern) : Int := if p 161 then d12 p else d2632 p
theorem agree2634 (p q : Pattern) (h : Agree support p q) : d2634 p = d2634 q := by
  simp only [d2634, h 161 (by decide), agree12 p q h, agree2632 p q h]
theorem nonnegative2634 (p : Pattern) : 0 ≤ d2634 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2632 p)
def d2635 (p : Pattern) : Int := if p 160 then d2634 p else d2633 p
theorem agree2635 (p q : Pattern) (h : Agree support p q) : d2635 p = d2635 q := by
  simp only [d2635, h 160 (by decide), agree2634 p q h, agree2633 p q h]
theorem nonnegative2635 (p : Pattern) : 0 ≤ d2635 p :=
  nonnegative_ite (p 160) (nonnegative2634 p) (nonnegative2633 p)
def d2636 (p : Pattern) : Int := if p 160 then d12 p else d2634 p
theorem agree2636 (p q : Pattern) (h : Agree support p q) : d2636 p = d2636 q := by
  simp only [d2636, h 160 (by decide), agree12 p q h, agree2634 p q h]
theorem nonnegative2636 (p : Pattern) : 0 ≤ d2636 p :=
  nonnegative_ite (p 160) (nonnegative12 p) (nonnegative2634 p)
def d2637 (p : Pattern) : Int := if p 141 then d2636 p else d2635 p
theorem agree2637 (p q : Pattern) (h : Agree support p q) : d2637 p = d2637 q := by
  simp only [d2637, h 141 (by decide), agree2636 p q h, agree2635 p q h]
theorem nonnegative2637 (p : Pattern) : 0 ≤ d2637 p :=
  nonnegative_ite (p 141) (nonnegative2636 p) (nonnegative2635 p)
def d2638 (p : Pattern) : Int := if p 138 then d2637 p else d2628 p
theorem agree2638 (p q : Pattern) (h : Agree support p q) : d2638 p = d2638 q := by
  simp only [d2638, h 138 (by decide), agree2637 p q h, agree2628 p q h]
theorem nonnegative2638 (p : Pattern) : 0 ≤ d2638 p :=
  nonnegative_ite (p 138) (nonnegative2637 p) (nonnegative2628 p)
def d2639 (p : Pattern) : Int := if p 116 then d2638 p else d2629 p
theorem agree2639 (p q : Pattern) (h : Agree support p q) : d2639 p = d2639 q := by
  simp only [d2639, h 116 (by decide), agree2638 p q h, agree2629 p q h]
theorem nonnegative2639 (p : Pattern) : 0 ≤ d2639 p :=
  nonnegative_ite (p 116) (nonnegative2638 p) (nonnegative2629 p)
end NetHack.Sokoban22Refined85
