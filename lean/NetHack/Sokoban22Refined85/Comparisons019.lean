/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2660 (p : Pattern) (guard : d1 p = 1) : d189 p ≤ (4 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d189, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2652 p hg
    simpa only [d189, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d189, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2659 p hg
    simpa only [d189, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2661 (p : Pattern) (guard : d1 p = 1) : d588 p ≤ (4 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2643 p hg
    simpa only [d588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2511 p hg
    simpa only [d588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2662 (p : Pattern) (guard : d1 p = 1) : d589 p ≤ (4 : Int) + d42 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d589, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2661 p hg
    simpa only [d589, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d589, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2527 p hg
    simpa only [d589, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2663 (p : Pattern) (guard : d1 p = 1) : d590 p ≤ (4 : Int) + d18 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2648 p hg
    simpa only [d590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2532 p hg
    simpa only [d590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2664 (p : Pattern) (guard : d1 p = 1) : d591 p ≤ (4 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d591, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2663 p hg
    simpa only [d591, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d591, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d591, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2665 (p : Pattern) (guard : d1 p = 1) : d592 p ≤ (4 : Int) + d44 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d592, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2662 p hg
    simpa only [d592, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d592, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2664 p hg
    simpa only [d592, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2666 (p : Pattern) (guard : d1 p = 1) : d593 p ≤ (4 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d593, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2523 p hg
    simpa only [d593, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d593, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2665 p hg
    simpa only [d593, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2667 (p : Pattern) (guard : d1 p = 1) : d589 p ≤ (4 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d589, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2661 p hg
    simpa only [d589, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d589, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d589, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2668 (p : Pattern) (guard : d1 p = 1) : d592 p ≤ (4 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d592, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2667 p hg
    simpa only [d592, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d592, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2664 p hg
    simpa only [d592, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2669 (p : Pattern) (guard : d1 p = 1) : d41 p ≤ (4 : Int) + d24 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2655 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2542 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2670 (p : Pattern) (guard : d1 p = 1) : d538 p ≤ (4 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d538, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2669 p hg
    simpa only [d538, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d538, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d538, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2671 (p : Pattern) (guard : d1 p = 1) : d539 p ≤ (4 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d539, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2670 p hg
    simpa only [d539, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d539, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d539, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2672 (p : Pattern) (guard : d1 p = 1) : d594 p ≤ (4 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d594, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2668 p hg
    simpa only [d594, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d594, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2671 p hg
    simpa only [d594, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2673 (p : Pattern) (guard : d1 p = 1) : d595 p ≤ (4 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d595, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2666 p hg
    simpa only [d595, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d595, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2672 p hg
    simpa only [d595, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2674 (p : Pattern) (guard : d1 p = 1) : d596 p ≤ (4 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d596, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2660 p hg
    simpa only [d596, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d596, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2673 p hg
    simpa only [d596, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2675 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (4 : Int) + d53 p := by
  omega
theorem compare2676 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (4 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2645 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2675 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2677 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (4 : Int) + d20 p := by
  omega
theorem compare2678 (p : Pattern) (guard : d1 p = 1) : d198 p ≤ (4 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d198, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2677 p hg
    simpa only [d198, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d198, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2657 p hg
    simpa only [d198, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2679 (p : Pattern) (guard : d1 p = 1) : d199 p ≤ (4 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d199, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2676 p hg
    simpa only [d199, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d199, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2678 p hg
    simpa only [d199, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2680 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2559 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2681 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2559 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2680 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2682 (p : Pattern) (guard : d1 p = 1) : d83 p ≤ (4 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d83, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2650 p hg
    simpa only [d83, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d83, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2681 p hg
    simpa only [d83, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2683 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2526 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2527 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2684 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2683 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2685 (p : Pattern) (guard : d1 p = 1) : d84 p ≤ (4 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d84, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2682 p hg
    simpa only [d84, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d84, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2684 p hg
    simpa only [d84, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2686 (p : Pattern) (guard : d1 p = 1) : d200 p ≤ (4 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d200, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2679 p hg
    simpa only [d200, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d200, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2685 p hg
    simpa only [d200, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2687 (p : Pattern) (guard : d1 p = 1) : d597 p ≤ (4 : Int) + d37 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d597, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2661 p hg
    simpa only [d597, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d597, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2521 p hg
    simpa only [d597, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2688 (p : Pattern) (guard : d1 p = 1) : d598 p ≤ (4 : Int) + d67 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d598, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2687 p hg
    simpa only [d598, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d598, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2552 p hg
    simpa only [d598, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2689 (p : Pattern) (guard : d1 p = 1) : d599 p ≤ (4 : Int) + d68 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d599, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2534 p hg
    simpa only [d599, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d599, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2670 p hg
    simpa only [d599, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2690 (p : Pattern) (guard : d1 p = 1) : d600 p ≤ (4 : Int) + d69 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d600, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2688 p hg
    simpa only [d600, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d600, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2689 p hg
    simpa only [d600, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2691 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2559 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2692 (p : Pattern) (guard : d1 p = 1) : d601 p ≤ (4 : Int) + d71 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d601, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2664 p hg
    simpa only [d601, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d601, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2691 p hg
    simpa only [d601, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2693 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2526 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2694 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d73 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2693 p hg
    simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2695 (p : Pattern) (guard : d1 p = 1) : d602 p ≤ (4 : Int) + d74 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d602, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2692 p hg
    simpa only [d602, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d602, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2694 p hg
    simpa only [d602, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2696 (p : Pattern) (guard : d1 p = 1) : d603 p ≤ (4 : Int) + d75 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d603, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2690 p hg
    simpa only [d603, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d603, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2695 p hg
    simpa only [d603, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2697 (p : Pattern) (guard : d1 p = 1) : d604 p ≤ (4 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d604, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2686 p hg
    simpa only [d604, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d604, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2696 p hg
    simpa only [d604, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2698 (p : Pattern) (guard : d1 p = 1) : d605 p ≤ (4 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d605, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2674 p hg
    simpa only [d605, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d605, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2697 p hg
    simpa only [d605, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2699 (p : Pattern) (guard : d4068 p = 1) : d606 p ≤ (4 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d606, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2698 p hg
    simpa only [d4068, d606, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d606, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2575 p hg
    simpa only [d4068, d606, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2700 (p : Pattern) (guard : d4069 p = 1) : d607 p ≤ (4 : Int) + d88 p := by
  cases selected : p 116 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4069, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2583 p hg
    simpa only [d4069, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4068 p = 1 := by simpa only [d4069, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2699 p hg
    simpa only [d4069, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2701 (p : Pattern) (guard : d4069 p = 1) : d608 p ≤ (4 : Int) + d88 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2582 p hg
    simpa only [d608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2700 p hg
    simpa only [d608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2702 (p : Pattern) (guard : d4069 p = 1) : d609 p ≤ (4 : Int) + d88 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2578 p hg
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2701 p hg
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2703 (p : Pattern) (guard : d0 p = 1) : d610 p ≤ (4 : Int) + d223 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2704 (p : Pattern) (guard : d1 p = 1) : d214 p ≤ (4 : Int) + d214 p := by
  omega
theorem compare2705 (p : Pattern) (guard : d1 p = 1) : d611 p ≤ (4 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d611, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2611 p hg
    simpa only [d611, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d611, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d611, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2706 (p : Pattern) (guard : d1 p = 1) : d612 p ≤ (4 : Int) + d216 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d612, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2622 p hg
    simpa only [d612, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d612, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2705 p hg
    simpa only [d612, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2707 (p : Pattern) (guard : d1 p = 1) : d613 p ≤ (4 : Int) + d217 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d613, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2705 p hg
    simpa only [d613, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d613, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d613, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2708 (p : Pattern) (guard : d1 p = 1) : d614 p ≤ (4 : Int) + d218 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d614, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2706 p hg
    simpa only [d614, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d614, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2707 p hg
    simpa only [d614, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2709 (p : Pattern) (guard : d1 p = 1) : d615 p ≤ (4 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d615, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2704 p hg
    simpa only [d615, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d615, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2708 p hg
    simpa only [d615, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2710 (p : Pattern) (guard : d1 p = 1) : d616 p ≤ (4 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d616, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2617 p hg
    simpa only [d616, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d616, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2709 p hg
    simpa only [d616, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2711 (p : Pattern) (guard : d0 p = 1) : d441 p ≤ (4 : Int) + d222 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2712 (p : Pattern) (guard : d4068 p = 1) : d617 p ≤ (4 : Int) + d223 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d617, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2710 p hg
    simpa only [d4068, d617, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d617, d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2711 p hg
    simpa only [d4068, d617, d223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2713 (p : Pattern) (guard : d4069 p = 1) : d618 p ≤ (4 : Int) + d223 p := by
  cases selected : p 116 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4069, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2703 p hg
    simpa only [d4069, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4068 p = 1 := by simpa only [d4069, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2712 p hg
    simpa only [d4069, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2714 (p : Pattern) (guard : d0 p = 1) : d619 p ≤ (4 : Int) + d306 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2715 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (4 : Int) + d105 p := by
  omega
theorem compare2716 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (4 : Int) + d1 p := by
  change (3 : Int) ≤ (4 : Int) + 1
  decide
theorem compare2717 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (4 : Int) + d102 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2716 p hg
    simpa only [d115, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d115, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2718 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (4 : Int) + d103 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2716 p hg
    simpa only [d116, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2717 p hg
    simpa only [d116, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2719 (p : Pattern) (guard : d1 p = 1) : d117 p ≤ (4 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d117, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2718 p hg
    simpa only [d117, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d117, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d117, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2720 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (4 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d132, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2718 p hg
    simpa only [d132, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d132, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2719 p hg
    simpa only [d132, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2721 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (4 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2609 p hg
    simpa only [d25, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d25, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2722 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (4 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2609 p hg
    simpa only [d26, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2721 p hg
    simpa only [d26, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2723 (p : Pattern) (guard : d1 p = 1) : d252 p ≤ (4 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d252, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2720 p hg
    simpa only [d252, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d252, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2722 p hg
    simpa only [d252, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2724 (p : Pattern) (guard : d1 p = 1) : d253 p ≤ (4 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d253, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2715 p hg
    simpa only [d253, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d253, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2723 p hg
    simpa only [d253, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2725 (p : Pattern) (guard : d1 p = 1) : d108 p ≤ (4 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d108, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2592 p hg
    simpa only [d108, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d108, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d108, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2726 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (4 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2592 p hg
    simpa only [d109, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2725 p hg
    simpa only [d109, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2727 (p : Pattern) (guard : d1 p = 1) : d254 p ≤ (4 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d254, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2726 p hg
    simpa only [d254, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d254, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2722 p hg
    simpa only [d254, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2728 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2681 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2729 (p : Pattern) (guard : d1 p = 1) : d255 p ≤ (4 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d255, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2727 p hg
    simpa only [d255, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d255, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2728 p hg
    simpa only [d255, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2730 (p : Pattern) (guard : d1 p = 1) : d256 p ≤ (4 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d256, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2724 p hg
    simpa only [d256, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d256, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2729 p hg
    simpa only [d256, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2731 (p : Pattern) (guard : d1 p = 1) : d620 p ≤ (4 : Int) + d268 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d620, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2589 p hg
    simpa only [d620, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d620, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2596 p hg
    simpa only [d620, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2732 (p : Pattern) (guard : d1 p = 1) : d621 p ≤ (4 : Int) + d269 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d621, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2731 p hg
    simpa only [d621, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d621, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2597 p hg
    simpa only [d621, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2733 (p : Pattern) (guard : d1 p = 1) : d622 p ≤ (4 : Int) + d270 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d622, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2731 p hg
    simpa only [d622, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d622, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2602 p hg
    simpa only [d622, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2734 (p : Pattern) (guard : d1 p = 1) : d623 p ≤ (4 : Int) + d271 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d623, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2732 p hg
    simpa only [d623, d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d623, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2733 p hg
    simpa only [d623, d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2735 (p : Pattern) (guard : d1 p = 1) : d570 p ≤ (4 : Int) + d268 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d570, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2718 p hg
    simpa only [d570, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d570, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2596 p hg
    simpa only [d570, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2736 (p : Pattern) (guard : d1 p = 1) : d571 p ≤ (4 : Int) + d272 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d571, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2735 p hg
    simpa only [d571, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d571, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d571, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2737 (p : Pattern) (guard : d1 p = 1) : d624 p ≤ (4 : Int) + d273 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d624, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2609 p hg
    simpa only [d624, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d624, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2601 p hg
    simpa only [d624, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2738 (p : Pattern) (guard : d1 p = 1) : d625 p ≤ (4 : Int) + d274 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d625, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2737 p hg
    simpa only [d625, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d625, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d625, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2739 (p : Pattern) (guard : d1 p = 1) : d626 p ≤ (4 : Int) + d275 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d626, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2736 p hg
    simpa only [d626, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d626, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2738 p hg
    simpa only [d626, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2740 (p : Pattern) (guard : d1 p = 1) : d627 p ≤ (4 : Int) + d276 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d627, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2734 p hg
    simpa only [d627, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d627, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2739 p hg
    simpa only [d627, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2741 (p : Pattern) (guard : d1 p = 1) : d273 p ≤ (4 : Int) + d268 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d273, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2592 p hg
    simpa only [d273, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d273, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2596 p hg
    simpa only [d273, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2742 (p : Pattern) (guard : d1 p = 1) : d274 p ≤ (4 : Int) + d272 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d274, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2741 p hg
    simpa only [d274, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d274, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d274, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2743 (p : Pattern) (guard : d1 p = 1) : d628 p ≤ (4 : Int) + d275 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d628, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2742 p hg
    simpa only [d628, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d628, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2738 p hg
    simpa only [d628, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2744 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d277 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2680 p hg
    simpa only [d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2745 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (4 : Int) + d278 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2744 p hg
    simpa only [d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2746 (p : Pattern) (guard : d1 p = 1) : d629 p ≤ (4 : Int) + d279 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d629, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2743 p hg
    simpa only [d629, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d629, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2745 p hg
    simpa only [d629, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2747 (p : Pattern) (guard : d1 p = 1) : d630 p ≤ (4 : Int) + d280 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d630, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2740 p hg
    simpa only [d630, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d630, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2746 p hg
    simpa only [d630, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2748 (p : Pattern) (guard : d1 p = 1) : d631 p ≤ (4 : Int) + d281 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d631, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2730 p hg
    simpa only [d631, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d631, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2747 p hg
    simpa only [d631, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2749 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (4 : Int) + d132 p := by
  omega
theorem compare2750 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (4 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2720 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2749 p hg
    simpa only [d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2751 (p : Pattern) (guard : d1 p = 1) : d211 p ≤ (4 : Int) + d211 p := by
  omega
theorem compare2752 (p : Pattern) (guard : d1 p = 1) : d245 p ≤ (4 : Int) + d212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d245, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2750 p hg
    simpa only [d245, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d245, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2751 p hg
    simpa only [d245, d212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2753 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (4 : Int) + d5 p := by
  change (7 : Int) ≤ (4 : Int) + 5
  decide
theorem compare2754 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (4 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2753 p hg
    simpa only [d119, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d119, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2755 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (4 : Int) + d107 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2753 p hg
    simpa only [d120, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2754 p hg
    simpa only [d120, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2756 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (4 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2755 p hg
    simpa only [d121, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d121, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2757 (p : Pattern) (guard : d1 p = 1) : d148 p ≤ (4 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d148, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2755 p hg
    simpa only [d148, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d148, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2756 p hg
    simpa only [d148, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2758 (p : Pattern) (guard : d1 p = 1) : d153 p ≤ (4 : Int) + d211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d153, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2757 p hg
    simpa only [d153, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d153, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d153, d211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2759 (p : Pattern) (guard : d1 p = 1) : d154 p ≤ (4 : Int) + d213 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d154, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2758 p hg
    simpa only [d154, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d154, d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d154, d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2760 (p : Pattern) (guard : d1 p = 1) : d246 p ≤ (4 : Int) + d214 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d246, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2752 p hg
    simpa only [d246, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d246, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2759 p hg
    simpa only [d246, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2761 (p : Pattern) (guard : d1 p = 1) : d632 p ≤ (4 : Int) + d270 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d632, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2735 p hg
    simpa only [d632, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d632, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2602 p hg
    simpa only [d632, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2762 (p : Pattern) (guard : d1 p = 1) : d633 p ≤ (4 : Int) + d282 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d633, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2619 p hg
    simpa only [d633, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d633, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2609 p hg
    simpa only [d633, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2763 (p : Pattern) (guard : d1 p = 1) : d634 p ≤ (4 : Int) + d283 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d634, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2762 p hg
    simpa only [d634, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d634, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d634, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2764 (p : Pattern) (guard : d1 p = 1) : d635 p ≤ (4 : Int) + d284 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d635, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2761 p hg
    simpa only [d635, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d635, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2763 p hg
    simpa only [d635, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2765 (p : Pattern) (guard : d1 p = 1) : d636 p ≤ (4 : Int) + d273 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d636, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2606 p hg
    simpa only [d636, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d636, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2601 p hg
    simpa only [d636, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2766 (p : Pattern) (guard : d1 p = 1) : d637 p ≤ (4 : Int) + d274 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d637, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2765 p hg
    simpa only [d637, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d637, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d637, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2767 (p : Pattern) (guard : d1 p = 1) : d638 p ≤ (4 : Int) + d285 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d638, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2766 p hg
    simpa only [d638, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d638, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d638, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2768 (p : Pattern) (guard : d1 p = 1) : d639 p ≤ (4 : Int) + d286 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d639, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2764 p hg
    simpa only [d639, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d639, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2767 p hg
    simpa only [d639, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2769 (p : Pattern) (guard : d1 p = 1) : d640 p ≤ (4 : Int) + d273 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d640, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2755 p hg
    simpa only [d640, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d640, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2601 p hg
    simpa only [d640, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2770 (p : Pattern) (guard : d1 p = 1) : d641 p ≤ (4 : Int) + d274 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d641, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2769 p hg
    simpa only [d641, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d641, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d641, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2771 (p : Pattern) (guard : d1 p = 1) : d642 p ≤ (4 : Int) + d285 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d642, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2770 p hg
    simpa only [d642, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d642, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d642, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2772 (p : Pattern) (guard : d1 p = 1) : d643 p ≤ (4 : Int) + d287 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d643, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2771 p hg
    simpa only [d643, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d643, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2509 p hg
    simpa only [d643, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2773 (p : Pattern) (guard : d1 p = 1) : d644 p ≤ (4 : Int) + d288 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d644, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2768 p hg
    simpa only [d644, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d644, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2772 p hg
    simpa only [d644, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2774 (p : Pattern) (guard : d1 p = 1) : d645 p ≤ (4 : Int) + d289 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d645, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2760 p hg
    simpa only [d645, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d645, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2773 p hg
    simpa only [d645, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2775 (p : Pattern) (guard : d1 p = 1) : d646 p ≤ (4 : Int) + d290 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d646, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2748 p hg
    simpa only [d646, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d646, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2774 p hg
    simpa only [d646, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2776 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d305 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2777 (p : Pattern) (guard : d4068 p = 1) : d647 p ≤ (4 : Int) + d306 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4068, d647, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2775 p hg
    simpa only [d4068, d647, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4068, d647, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2776 p hg
    simpa only [d4068, d647, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2778 (p : Pattern) (guard : d4069 p = 1) : d648 p ≤ (4 : Int) + d306 p := by
  cases selected : p 116 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4069, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2714 p hg
    simpa only [d4069, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4068 p = 1 := by simpa only [d4069, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2777 p hg
    simpa only [d4069, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2779 (p : Pattern) (guard : d4069 p = 1) : d649 p ≤ (4 : Int) + d4199 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d649, d4199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2713 p hg
    simpa only [d649, d4199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d649, d4199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2778 p hg
    simpa only [d649, d4199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2780 (p : Pattern) (guard : d4069 p = 1) : d650 p ≤ (4 : Int) + d4200 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d650, d4200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2578 p hg
    simpa only [d650, d4200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d650, d4200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2779 p hg
    simpa only [d650, d4200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2781 (p : Pattern) (guard : d4069 p = 1) : d651 p ≤ (4 : Int) + d4201 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d651, d4201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2702 p hg
    simpa only [d651, d4201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d651, d4201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2780 p hg
    simpa only [d651, d4201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2782 (p : Pattern) (guard : d4069 p = 1) : d652 p ≤ (4 : Int) + d4202 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4069 p = 1 := by simpa only [d652, d4202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2639 p hg
    simpa only [d652, d4202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4069 p = 1 := by simpa only [d652, d4202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2781 p hg
    simpa only [d652, d4202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2783 (p : Pattern) (guard : d0 p = 1) : d51 p ≤ (0 : Int) + d376 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2784 (p : Pattern) (guard : d4117 p = 1) : d52 p ≤ (0 : Int) + d710 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d52, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d52, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d52, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2783 p hg
    simpa only [d4117, d52, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2785 (p : Pattern) (guard : d0 p = 1) : d75 p ≤ (0 : Int) + d391 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2786 (p : Pattern) (guard : d4117 p = 1) : d76 p ≤ (0 : Int) + d711 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d76, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d4117, d76, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d76, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2785 p hg
    simpa only [d4117, d76, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2787 (p : Pattern) (guard : d4117 p = 1) : d77 p ≤ (0 : Int) + d712 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d77, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2784 p hg
    simpa only [d77, d712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d77, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2786 p hg
    simpa only [d77, d712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2788 (p : Pattern) (guard : d0 p = 1) : d400 p ≤ (0 : Int) + d715 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2789 (p : Pattern) (guard : d4203 p = 1) : d517 p ≤ (0 : Int) + d716 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d517, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2787 p hg
    simpa only [d4203, d517, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d517, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2788 p hg
    simpa only [d4203, d517, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2790 (p : Pattern) (guard : d0 p = 1) : d530 p ≤ (0 : Int) + d405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2791 (p : Pattern) (guard : d4117 p = 1) : d531 p ≤ (0 : Int) + d717 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d531, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d531, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d531, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2790 p hg
    simpa only [d4117, d531, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2792 (p : Pattern) (guard : d0 p = 1) : d541 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2793 (p : Pattern) (guard : d4117 p = 1) : d542 p ≤ (0 : Int) + d714 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d542, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d4117, d542, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d542, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2792 p hg
    simpa only [d4117, d542, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2794 (p : Pattern) (guard : d4117 p = 1) : d543 p ≤ (0 : Int) + d718 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d543, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2791 p hg
    simpa only [d543, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d543, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2793 p hg
    simpa only [d543, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2795 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (0 : Int) + d720 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2796 (p : Pattern) (guard : d4203 p = 1) : d544 p ≤ (0 : Int) + d721 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d544, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2794 p hg
    simpa only [d4203, d544, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d544, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2795 p hg
    simpa only [d4203, d544, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2797 (p : Pattern) (guard : d4203 p = 1) : d545 p ≤ (0 : Int) + d722 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d545, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2789 p hg
    simpa only [d545, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d545, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2796 p hg
    simpa only [d545, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2798 (p : Pattern) (guard : d0 p = 1) : d51 p ≤ (0 : Int) + d409 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2799 (p : Pattern) (guard : d4117 p = 1) : d52 p ≤ (0 : Int) + d723 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d52, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d52, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d52, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2798 p hg
    simpa only [d4117, d52, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
