/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Nodes21
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
def d2640 (p : Pattern) : Int := if p 163 then d2519 p else d2516 p
theorem agree2640 (p q : Pattern) (h : Agree support p q) : d2640 p = d2640 q := by
  simp only [d2640, h 163 (by decide), agree2519 p q h, agree2516 p q h]
theorem nonnegative2640 (p : Pattern) : 0 ≤ d2640 p :=
  nonnegative_ite (p 163) (nonnegative2519 p) (nonnegative2516 p)
def d2641 (p : Pattern) : Int := if p 162 then d2528 p else d2640 p
theorem agree2641 (p q : Pattern) (h : Agree support p q) : d2641 p = d2641 q := by
  simp only [d2641, h 162 (by decide), agree2528 p q h, agree2640 p q h]
theorem nonnegative2641 (p : Pattern) : 0 ≤ d2641 p :=
  nonnegative_ite (p 162) (nonnegative2528 p) (nonnegative2640 p)
def d2642 (p : Pattern) : Int := if p 161 then d2538 p else d2641 p
theorem agree2642 (p q : Pattern) (h : Agree support p q) : d2642 p = d2642 q := by
  simp only [d2642, h 161 (by decide), agree2538 p q h, agree2641 p q h]
theorem nonnegative2642 (p : Pattern) : 0 ≤ d2642 p :=
  nonnegative_ite (p 161) (nonnegative2538 p) (nonnegative2641 p)
def d2643 (p : Pattern) : Int := if p 160 then d2563 p else d2642 p
theorem agree2643 (p q : Pattern) (h : Agree support p q) : d2643 p = d2643 q := by
  simp only [d2643, h 160 (by decide), agree2563 p q h, agree2642 p q h]
theorem nonnegative2643 (p : Pattern) : 0 ≤ d2643 p :=
  nonnegative_ite (p 160) (nonnegative2563 p) (nonnegative2642 p)
def d2644 (p : Pattern) : Int := if p 163 then d2573 p else d2519 p
theorem agree2644 (p q : Pattern) (h : Agree support p q) : d2644 p = d2644 q := by
  simp only [d2644, h 163 (by decide), agree2573 p q h, agree2519 p q h]
theorem nonnegative2644 (p : Pattern) : 0 ≤ d2644 p :=
  nonnegative_ite (p 163) (nonnegative2573 p) (nonnegative2519 p)
def d2645 (p : Pattern) : Int := if p 162 then d2575 p else d2644 p
theorem agree2645 (p q : Pattern) (h : Agree support p q) : d2645 p = d2645 q := by
  simp only [d2645, h 162 (by decide), agree2575 p q h, agree2644 p q h]
theorem nonnegative2645 (p : Pattern) : 0 ≤ d2645 p :=
  nonnegative_ite (p 162) (nonnegative2575 p) (nonnegative2644 p)
def d2646 (p : Pattern) : Int := if p 161 then d2586 p else d2645 p
theorem agree2646 (p q : Pattern) (h : Agree support p q) : d2646 p = d2646 q := by
  simp only [d2646, h 161 (by decide), agree2586 p q h, agree2645 p q h]
theorem nonnegative2646 (p : Pattern) : 0 ≤ d2646 p :=
  nonnegative_ite (p 161) (nonnegative2586 p) (nonnegative2645 p)
def d2647 (p : Pattern) : Int := if p 160 then d2597 p else d2646 p
theorem agree2647 (p q : Pattern) (h : Agree support p q) : d2647 p = d2647 q := by
  simp only [d2647, h 160 (by decide), agree2597 p q h, agree2646 p q h]
theorem nonnegative2647 (p : Pattern) : 0 ≤ d2647 p :=
  nonnegative_ite (p 160) (nonnegative2597 p) (nonnegative2646 p)
def d2648 (p : Pattern) : Int := if p 141 then d2647 p else d2643 p
theorem agree2648 (p q : Pattern) (h : Agree support p q) : d2648 p = d2648 q := by
  simp only [d2648, h 141 (by decide), agree2647 p q h, agree2643 p q h]
theorem nonnegative2648 (p : Pattern) : 0 ≤ d2648 p :=
  nonnegative_ite (p 141) (nonnegative2647 p) (nonnegative2643 p)
def d2649 (p : Pattern) : Int := if p 138 then d2628 p else d2648 p
theorem agree2649 (p q : Pattern) (h : Agree support p q) : d2649 p = d2649 q := by
  simp only [d2649, h 138 (by decide), agree2628 p q h, agree2648 p q h]
theorem nonnegative2649 (p : Pattern) : 0 ≤ d2649 p :=
  nonnegative_ite (p 138) (nonnegative2628 p) (nonnegative2648 p)
def d2650 (p : Pattern) : Int := if p 138 then d12 p else d2628 p
theorem agree2650 (p q : Pattern) (h : Agree support p q) : d2650 p = d2650 q := by
  simp only [d2650, h 138 (by decide), agree12 p q h, agree2628 p q h]
theorem nonnegative2650 (p : Pattern) : 0 ≤ d2650 p :=
  nonnegative_ite (p 138) (nonnegative12 p) (nonnegative2628 p)
def d2651 (p : Pattern) : Int := if p 116 then d2650 p else d2649 p
theorem agree2651 (p q : Pattern) (h : Agree support p q) : d2651 p = d2651 q := by
  simp only [d2651, h 116 (by decide), agree2650 p q h, agree2649 p q h]
theorem nonnegative2651 (p : Pattern) : 0 ≤ d2651 p :=
  nonnegative_ite (p 116) (nonnegative2650 p) (nonnegative2649 p)
def d2652 (p : Pattern) : Int := if p 115 then d2651 p else d2639 p
theorem agree2652 (p q : Pattern) (h : Agree support p q) : d2652 p = d2652 q := by
  simp only [d2652, h 115 (by decide), agree2651 p q h, agree2639 p q h]
theorem nonnegative2652 (p : Pattern) : 0 ≤ d2652 p :=
  nonnegative_ite (p 115) (nonnegative2651 p) (nonnegative2639 p)
def d2653 (p : Pattern) : Int := if p 225 then d356 p else d14 p
theorem agree2653 (p q : Pattern) (h : Agree support p q) : d2653 p = d2653 q := by
  simp only [d2653, h 225 (by decide), agree356 p q h, agree14 p q h]
theorem nonnegative2653 (p : Pattern) : 0 ≤ d2653 p :=
  nonnegative_ite (p 225) (nonnegative356 p) (nonnegative14 p)
def d2654 (p : Pattern) : Int := if p 224 then d2504 p else d2653 p
theorem agree2654 (p q : Pattern) (h : Agree support p q) : d2654 p = d2654 q := by
  simp only [d2654, h 224 (by decide), agree2504 p q h, agree2653 p q h]
theorem nonnegative2654 (p : Pattern) : 0 ≤ d2654 p :=
  nonnegative_ite (p 224) (nonnegative2504 p) (nonnegative2653 p)
def d2655 (p : Pattern) : Int := if p 204 then d2507 p else d2654 p
theorem agree2655 (p q : Pattern) (h : Agree support p q) : d2655 p = d2655 q := by
  simp only [d2655, h 204 (by decide), agree2507 p q h, agree2654 p q h]
theorem nonnegative2655 (p : Pattern) : 0 ≤ d2655 p :=
  nonnegative_ite (p 204) (nonnegative2507 p) (nonnegative2654 p)
def d2656 (p : Pattern) : Int := if p 182 then d2511 p else d2655 p
theorem agree2656 (p q : Pattern) (h : Agree support p q) : d2656 p = d2656 q := by
  simp only [d2656, h 182 (by decide), agree2511 p q h, agree2655 p q h]
theorem nonnegative2656 (p : Pattern) : 0 ≤ d2656 p :=
  nonnegative_ite (p 182) (nonnegative2511 p) (nonnegative2655 p)
def d2657 (p : Pattern) : Int := if p 163 then d2519 p else d2656 p
theorem agree2657 (p q : Pattern) (h : Agree support p q) : d2657 p = d2657 q := by
  simp only [d2657, h 163 (by decide), agree2519 p q h, agree2656 p q h]
theorem nonnegative2657 (p : Pattern) : 0 ≤ d2657 p :=
  nonnegative_ite (p 163) (nonnegative2519 p) (nonnegative2656 p)
def d2658 (p : Pattern) : Int := if p 162 then d2528 p else d2657 p
theorem agree2658 (p q : Pattern) (h : Agree support p q) : d2658 p = d2658 q := by
  simp only [d2658, h 162 (by decide), agree2528 p q h, agree2657 p q h]
theorem nonnegative2658 (p : Pattern) : 0 ≤ d2658 p :=
  nonnegative_ite (p 162) (nonnegative2528 p) (nonnegative2657 p)
def d2659 (p : Pattern) : Int := if p 161 then d2538 p else d2658 p
theorem agree2659 (p q : Pattern) (h : Agree support p q) : d2659 p = d2659 q := by
  simp only [d2659, h 161 (by decide), agree2538 p q h, agree2658 p q h]
theorem nonnegative2659 (p : Pattern) : 0 ≤ d2659 p :=
  nonnegative_ite (p 161) (nonnegative2538 p) (nonnegative2658 p)
def d2660 (p : Pattern) : Int := if p 160 then d2563 p else d2659 p
theorem agree2660 (p q : Pattern) (h : Agree support p q) : d2660 p = d2660 q := by
  simp only [d2660, h 160 (by decide), agree2563 p q h, agree2659 p q h]
theorem nonnegative2660 (p : Pattern) : 0 ≤ d2660 p :=
  nonnegative_ite (p 160) (nonnegative2563 p) (nonnegative2659 p)
def d2661 (p : Pattern) : Int := if p 163 then d2573 p else d2516 p
theorem agree2661 (p q : Pattern) (h : Agree support p q) : d2661 p = d2661 q := by
  simp only [d2661, h 163 (by decide), agree2573 p q h, agree2516 p q h]
theorem nonnegative2661 (p : Pattern) : 0 ≤ d2661 p :=
  nonnegative_ite (p 163) (nonnegative2573 p) (nonnegative2516 p)
def d2662 (p : Pattern) : Int := if p 162 then d2575 p else d2661 p
theorem agree2662 (p q : Pattern) (h : Agree support p q) : d2662 p = d2662 q := by
  simp only [d2662, h 162 (by decide), agree2575 p q h, agree2661 p q h]
theorem nonnegative2662 (p : Pattern) : 0 ≤ d2662 p :=
  nonnegative_ite (p 162) (nonnegative2575 p) (nonnegative2661 p)
def d2663 (p : Pattern) : Int := if p 161 then d2586 p else d2662 p
theorem agree2663 (p q : Pattern) (h : Agree support p q) : d2663 p = d2663 q := by
  simp only [d2663, h 161 (by decide), agree2586 p q h, agree2662 p q h]
theorem nonnegative2663 (p : Pattern) : 0 ≤ d2663 p :=
  nonnegative_ite (p 161) (nonnegative2586 p) (nonnegative2662 p)
def d2664 (p : Pattern) : Int := if p 160 then d2597 p else d2663 p
theorem agree2664 (p q : Pattern) (h : Agree support p q) : d2664 p = d2664 q := by
  simp only [d2664, h 160 (by decide), agree2597 p q h, agree2663 p q h]
theorem nonnegative2664 (p : Pattern) : 0 ≤ d2664 p :=
  nonnegative_ite (p 160) (nonnegative2597 p) (nonnegative2663 p)
def d2665 (p : Pattern) : Int := if p 141 then d2664 p else d2660 p
theorem agree2665 (p q : Pattern) (h : Agree support p q) : d2665 p = d2665 q := by
  simp only [d2665, h 141 (by decide), agree2664 p q h, agree2660 p q h]
theorem nonnegative2665 (p : Pattern) : 0 ≤ d2665 p :=
  nonnegative_ite (p 141) (nonnegative2664 p) (nonnegative2660 p)
def d2666 (p : Pattern) : Int := if p 138 then d2628 p else d2665 p
theorem agree2666 (p q : Pattern) (h : Agree support p q) : d2666 p = d2666 q := by
  simp only [d2666, h 138 (by decide), agree2628 p q h, agree2665 p q h]
theorem nonnegative2666 (p : Pattern) : 0 ≤ d2666 p :=
  nonnegative_ite (p 138) (nonnegative2628 p) (nonnegative2665 p)
def d2667 (p : Pattern) : Int := if p 116 then d2638 p else d2666 p
theorem agree2667 (p q : Pattern) (h : Agree support p q) : d2667 p = d2667 q := by
  simp only [d2667, h 116 (by decide), agree2638 p q h, agree2666 p q h]
theorem nonnegative2667 (p : Pattern) : 0 ≤ d2667 p :=
  nonnegative_ite (p 116) (nonnegative2638 p) (nonnegative2666 p)
def d2668 (p : Pattern) : Int := if p 162 then d2528 p else d2519 p
theorem agree2668 (p q : Pattern) (h : Agree support p q) : d2668 p = d2668 q := by
  simp only [d2668, h 162 (by decide), agree2528 p q h, agree2519 p q h]
theorem nonnegative2668 (p : Pattern) : 0 ≤ d2668 p :=
  nonnegative_ite (p 162) (nonnegative2528 p) (nonnegative2519 p)
def d2669 (p : Pattern) : Int := if p 161 then d2538 p else d2668 p
theorem agree2669 (p q : Pattern) (h : Agree support p q) : d2669 p = d2669 q := by
  simp only [d2669, h 161 (by decide), agree2538 p q h, agree2668 p q h]
theorem nonnegative2669 (p : Pattern) : 0 ≤ d2669 p :=
  nonnegative_ite (p 161) (nonnegative2538 p) (nonnegative2668 p)
def d2670 (p : Pattern) : Int := if p 160 then d2563 p else d2669 p
theorem agree2670 (p q : Pattern) (h : Agree support p q) : d2670 p = d2670 q := by
  simp only [d2670, h 160 (by decide), agree2563 p q h, agree2669 p q h]
theorem nonnegative2670 (p : Pattern) : 0 ≤ d2670 p :=
  nonnegative_ite (p 160) (nonnegative2563 p) (nonnegative2669 p)
def d2671 (p : Pattern) : Int := if p 141 then d2647 p else d2670 p
theorem agree2671 (p q : Pattern) (h : Agree support p q) : d2671 p = d2671 q := by
  simp only [d2671, h 141 (by decide), agree2647 p q h, agree2670 p q h]
theorem nonnegative2671 (p : Pattern) : 0 ≤ d2671 p :=
  nonnegative_ite (p 141) (nonnegative2647 p) (nonnegative2670 p)
def d2672 (p : Pattern) : Int := if p 138 then d2628 p else d2671 p
theorem agree2672 (p q : Pattern) (h : Agree support p q) : d2672 p = d2672 q := by
  simp only [d2672, h 138 (by decide), agree2628 p q h, agree2671 p q h]
theorem nonnegative2672 (p : Pattern) : 0 ≤ d2672 p :=
  nonnegative_ite (p 138) (nonnegative2628 p) (nonnegative2671 p)
def d2673 (p : Pattern) : Int := if p 116 then d2650 p else d2672 p
theorem agree2673 (p q : Pattern) (h : Agree support p q) : d2673 p = d2673 q := by
  simp only [d2673, h 116 (by decide), agree2650 p q h, agree2672 p q h]
theorem nonnegative2673 (p : Pattern) : 0 ≤ d2673 p :=
  nonnegative_ite (p 116) (nonnegative2650 p) (nonnegative2672 p)
def d2674 (p : Pattern) : Int := if p 115 then d2673 p else d2667 p
theorem agree2674 (p q : Pattern) (h : Agree support p q) : d2674 p = d2674 q := by
  simp only [d2674, h 115 (by decide), agree2673 p q h, agree2667 p q h]
theorem nonnegative2674 (p : Pattern) : 0 ≤ d2674 p :=
  nonnegative_ite (p 115) (nonnegative2673 p) (nonnegative2667 p)
def d2675 (p : Pattern) : Int := if p 71 then d2674 p else d2652 p
theorem agree2675 (p q : Pattern) (h : Agree support p q) : d2675 p = d2675 q := by
  simp only [d2675, h 71 (by decide), agree2674 p q h, agree2652 p q h]
theorem nonnegative2675 (p : Pattern) : 0 ≤ d2675 p :=
  nonnegative_ite (p 71) (nonnegative2674 p) (nonnegative2652 p)
def d2676 (p : Pattern) : Int := if p 225 then d356 p else d103 p
theorem agree2676 (p q : Pattern) (h : Agree support p q) : d2676 p = d2676 q := by
  simp only [d2676, h 225 (by decide), agree356 p q h, agree103 p q h]
theorem nonnegative2676 (p : Pattern) : 0 ≤ d2676 p :=
  nonnegative_ite (p 225) (nonnegative356 p) (nonnegative103 p)
def d2677 (p : Pattern) : Int := if p 225 then d12 p else d103 p
theorem agree2677 (p q : Pattern) (h : Agree support p q) : d2677 p = d2677 q := by
  simp only [d2677, h 225 (by decide), agree12 p q h, agree103 p q h]
theorem nonnegative2677 (p : Pattern) : 0 ≤ d2677 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative103 p)
def d2678 (p : Pattern) : Int := if p 224 then d2677 p else d2676 p
theorem agree2678 (p q : Pattern) (h : Agree support p q) : d2678 p = d2678 q := by
  simp only [d2678, h 224 (by decide), agree2677 p q h, agree2676 p q h]
theorem nonnegative2678 (p : Pattern) : 0 ≤ d2678 p :=
  nonnegative_ite (p 224) (nonnegative2677 p) (nonnegative2676 p)
def d2679 (p : Pattern) : Int := if p 225 then d12 p else d1940 p
theorem agree2679 (p q : Pattern) (h : Agree support p q) : d2679 p = d2679 q := by
  simp only [d2679, h 225 (by decide), agree12 p q h, agree1940 p q h]
theorem nonnegative2679 (p : Pattern) : 0 ≤ d2679 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative1940 p)
def d2680 (p : Pattern) : Int := if p 224 then d2679 p else d2677 p
theorem agree2680 (p q : Pattern) (h : Agree support p q) : d2680 p = d2680 q := by
  simp only [d2680, h 224 (by decide), agree2679 p q h, agree2677 p q h]
theorem nonnegative2680 (p : Pattern) : 0 ≤ d2680 p :=
  nonnegative_ite (p 224) (nonnegative2679 p) (nonnegative2677 p)
def d2681 (p : Pattern) : Int := if p 204 then d2680 p else d2678 p
theorem agree2681 (p q : Pattern) (h : Agree support p q) : d2681 p = d2681 q := by
  simp only [d2681, h 204 (by decide), agree2680 p q h, agree2678 p q h]
theorem nonnegative2681 (p : Pattern) : 0 ≤ d2681 p :=
  nonnegative_ite (p 204) (nonnegative2680 p) (nonnegative2678 p)
def d2682 (p : Pattern) : Int := if p 225 then d12 p else d1873 p
theorem agree2682 (p q : Pattern) (h : Agree support p q) : d2682 p = d2682 q := by
  simp only [d2682, h 225 (by decide), agree12 p q h, agree1873 p q h]
theorem nonnegative2682 (p : Pattern) : 0 ≤ d2682 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative1873 p)
def d2683 (p : Pattern) : Int := if p 224 then d2682 p else d2677 p
theorem agree2683 (p q : Pattern) (h : Agree support p q) : d2683 p = d2683 q := by
  simp only [d2683, h 224 (by decide), agree2682 p q h, agree2677 p q h]
theorem nonnegative2683 (p : Pattern) : 0 ≤ d2683 p :=
  nonnegative_ite (p 224) (nonnegative2682 p) (nonnegative2677 p)
def d2684 (p : Pattern) : Int := if p 204 then d12 p else d2683 p
theorem agree2684 (p q : Pattern) (h : Agree support p q) : d2684 p = d2684 q := by
  simp only [d2684, h 204 (by decide), agree12 p q h, agree2683 p q h]
theorem nonnegative2684 (p : Pattern) : 0 ≤ d2684 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2683 p)
def d2685 (p : Pattern) : Int := if p 182 then d2684 p else d2681 p
theorem agree2685 (p q : Pattern) (h : Agree support p q) : d2685 p = d2685 q := by
  simp only [d2685, h 182 (by decide), agree2684 p q h, agree2681 p q h]
theorem nonnegative2685 (p : Pattern) : 0 ≤ d2685 p :=
  nonnegative_ite (p 182) (nonnegative2684 p) (nonnegative2681 p)
def d2686 (p : Pattern) : Int := if p 204 then d2680 p else d2677 p
theorem agree2686 (p q : Pattern) (h : Agree support p q) : d2686 p = d2686 q := by
  simp only [d2686, h 204 (by decide), agree2680 p q h, agree2677 p q h]
theorem nonnegative2686 (p : Pattern) : 0 ≤ d2686 p :=
  nonnegative_ite (p 204) (nonnegative2680 p) (nonnegative2677 p)
def d2687 (p : Pattern) : Int := if p 182 then d2684 p else d2686 p
theorem agree2687 (p q : Pattern) (h : Agree support p q) : d2687 p = d2687 q := by
  simp only [d2687, h 182 (by decide), agree2684 p q h, agree2686 p q h]
theorem nonnegative2687 (p : Pattern) : 0 ≤ d2687 p :=
  nonnegative_ite (p 182) (nonnegative2684 p) (nonnegative2686 p)
def d2688 (p : Pattern) : Int := if p 163 then d2687 p else d2685 p
theorem agree2688 (p q : Pattern) (h : Agree support p q) : d2688 p = d2688 q := by
  simp only [d2688, h 163 (by decide), agree2687 p q h, agree2685 p q h]
theorem nonnegative2688 (p : Pattern) : 0 ≤ d2688 p :=
  nonnegative_ite (p 163) (nonnegative2687 p) (nonnegative2685 p)
def d2689 (p : Pattern) : Int := if p 225 then d12 p else d107 p
theorem agree2689 (p q : Pattern) (h : Agree support p q) : d2689 p = d2689 q := by
  simp only [d2689, h 225 (by decide), agree12 p q h, agree107 p q h]
theorem nonnegative2689 (p : Pattern) : 0 ≤ d2689 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative107 p)
def d2690 (p : Pattern) : Int := if p 225 then d12 p else d1964 p
theorem agree2690 (p q : Pattern) (h : Agree support p q) : d2690 p = d2690 q := by
  simp only [d2690, h 225 (by decide), agree12 p q h, agree1964 p q h]
theorem nonnegative2690 (p : Pattern) : 0 ≤ d2690 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative1964 p)
def d2691 (p : Pattern) : Int := if p 224 then d2690 p else d2689 p
theorem agree2691 (p q : Pattern) (h : Agree support p q) : d2691 p = d2691 q := by
  simp only [d2691, h 224 (by decide), agree2690 p q h, agree2689 p q h]
theorem nonnegative2691 (p : Pattern) : 0 ≤ d2691 p :=
  nonnegative_ite (p 224) (nonnegative2690 p) (nonnegative2689 p)
def d2692 (p : Pattern) : Int := if p 204 then d2691 p else d2689 p
theorem agree2692 (p q : Pattern) (h : Agree support p q) : d2692 p = d2692 q := by
  simp only [d2692, h 204 (by decide), agree2691 p q h, agree2689 p q h]
theorem nonnegative2692 (p : Pattern) : 0 ≤ d2692 p :=
  nonnegative_ite (p 204) (nonnegative2691 p) (nonnegative2689 p)
def d2693 (p : Pattern) : Int := if p 225 then d12 p else d1881 p
theorem agree2693 (p q : Pattern) (h : Agree support p q) : d2693 p = d2693 q := by
  simp only [d2693, h 225 (by decide), agree12 p q h, agree1881 p q h]
theorem nonnegative2693 (p : Pattern) : 0 ≤ d2693 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative1881 p)
def d2694 (p : Pattern) : Int := if p 224 then d2693 p else d2689 p
theorem agree2694 (p q : Pattern) (h : Agree support p q) : d2694 p = d2694 q := by
  simp only [d2694, h 224 (by decide), agree2693 p q h, agree2689 p q h]
theorem nonnegative2694 (p : Pattern) : 0 ≤ d2694 p :=
  nonnegative_ite (p 224) (nonnegative2693 p) (nonnegative2689 p)
def d2695 (p : Pattern) : Int := if p 204 then d12 p else d2694 p
theorem agree2695 (p q : Pattern) (h : Agree support p q) : d2695 p = d2695 q := by
  simp only [d2695, h 204 (by decide), agree12 p q h, agree2694 p q h]
theorem nonnegative2695 (p : Pattern) : 0 ≤ d2695 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2694 p)
def d2696 (p : Pattern) : Int := if p 182 then d2695 p else d2692 p
theorem agree2696 (p q : Pattern) (h : Agree support p q) : d2696 p = d2696 q := by
  simp only [d2696, h 182 (by decide), agree2695 p q h, agree2692 p q h]
theorem nonnegative2696 (p : Pattern) : 0 ≤ d2696 p :=
  nonnegative_ite (p 182) (nonnegative2695 p) (nonnegative2692 p)
def d2697 (p : Pattern) : Int := if p 163 then d2696 p else d2687 p
theorem agree2697 (p q : Pattern) (h : Agree support p q) : d2697 p = d2697 q := by
  simp only [d2697, h 163 (by decide), agree2696 p q h, agree2687 p q h]
theorem nonnegative2697 (p : Pattern) : 0 ≤ d2697 p :=
  nonnegative_ite (p 163) (nonnegative2696 p) (nonnegative2687 p)
def d2698 (p : Pattern) : Int := if p 162 then d2697 p else d2688 p
theorem agree2698 (p q : Pattern) (h : Agree support p q) : d2698 p = d2698 q := by
  simp only [d2698, h 162 (by decide), agree2697 p q h, agree2688 p q h]
theorem nonnegative2698 (p : Pattern) : 0 ≤ d2698 p :=
  nonnegative_ite (p 162) (nonnegative2697 p) (nonnegative2688 p)
def d2699 (p : Pattern) : Int := if p 163 then d12 p else d2581 p
theorem agree2699 (p q : Pattern) (h : Agree support p q) : d2699 p = d2699 q := by
  simp only [d2699, h 163 (by decide), agree12 p q h, agree2581 p q h]
theorem nonnegative2699 (p : Pattern) : 0 ≤ d2699 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2581 p)
def d2700 (p : Pattern) : Int := if p 162 then d2699 p else d2697 p
theorem agree2700 (p q : Pattern) (h : Agree support p q) : d2700 p = d2700 q := by
  simp only [d2700, h 162 (by decide), agree2699 p q h, agree2697 p q h]
theorem nonnegative2700 (p : Pattern) : 0 ≤ d2700 p :=
  nonnegative_ite (p 162) (nonnegative2699 p) (nonnegative2697 p)
def d2701 (p : Pattern) : Int := if p 161 then d2700 p else d2698 p
theorem agree2701 (p q : Pattern) (h : Agree support p q) : d2701 p = d2701 q := by
  simp only [d2701, h 161 (by decide), agree2700 p q h, agree2698 p q h]
theorem nonnegative2701 (p : Pattern) : 0 ≤ d2701 p :=
  nonnegative_ite (p 161) (nonnegative2700 p) (nonnegative2698 p)
def d2702 (p : Pattern) : Int := if p 225 then d12 p else d116 p
theorem agree2702 (p q : Pattern) (h : Agree support p q) : d2702 p = d2702 q := by
  simp only [d2702, h 225 (by decide), agree12 p q h, agree116 p q h]
theorem nonnegative2702 (p : Pattern) : 0 ≤ d2702 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative116 p)
def d2703 (p : Pattern) : Int := if p 225 then d12 p else d1895 p
theorem agree2703 (p q : Pattern) (h : Agree support p q) : d2703 p = d2703 q := by
  simp only [d2703, h 225 (by decide), agree12 p q h, agree1895 p q h]
theorem nonnegative2703 (p : Pattern) : 0 ≤ d2703 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative1895 p)
def d2704 (p : Pattern) : Int := if p 224 then d2703 p else d2702 p
theorem agree2704 (p q : Pattern) (h : Agree support p q) : d2704 p = d2704 q := by
  simp only [d2704, h 224 (by decide), agree2703 p q h, agree2702 p q h]
theorem nonnegative2704 (p : Pattern) : 0 ≤ d2704 p :=
  nonnegative_ite (p 224) (nonnegative2703 p) (nonnegative2702 p)
def d2705 (p : Pattern) : Int := if p 204 then d12 p else d2704 p
theorem agree2705 (p q : Pattern) (h : Agree support p q) : d2705 p = d2705 q := by
  simp only [d2705, h 204 (by decide), agree12 p q h, agree2704 p q h]
theorem nonnegative2705 (p : Pattern) : 0 ≤ d2705 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2704 p)
def d2706 (p : Pattern) : Int := if p 182 then d2705 p else d2686 p
theorem agree2706 (p q : Pattern) (h : Agree support p q) : d2706 p = d2706 q := by
  simp only [d2706, h 182 (by decide), agree2705 p q h, agree2686 p q h]
theorem nonnegative2706 (p : Pattern) : 0 ≤ d2706 p :=
  nonnegative_ite (p 182) (nonnegative2705 p) (nonnegative2686 p)
def d2707 (p : Pattern) : Int := if p 225 then d12 p else d120 p
theorem agree2707 (p q : Pattern) (h : Agree support p q) : d2707 p = d2707 q := by
  simp only [d2707, h 225 (by decide), agree12 p q h, agree120 p q h]
theorem nonnegative2707 (p : Pattern) : 0 ≤ d2707 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative120 p)
def d2708 (p : Pattern) : Int := if p 225 then d12 p else d1903 p
theorem agree2708 (p q : Pattern) (h : Agree support p q) : d2708 p = d2708 q := by
  simp only [d2708, h 225 (by decide), agree12 p q h, agree1903 p q h]
theorem nonnegative2708 (p : Pattern) : 0 ≤ d2708 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative1903 p)
def d2709 (p : Pattern) : Int := if p 224 then d2708 p else d2707 p
theorem agree2709 (p q : Pattern) (h : Agree support p q) : d2709 p = d2709 q := by
  simp only [d2709, h 224 (by decide), agree2708 p q h, agree2707 p q h]
theorem nonnegative2709 (p : Pattern) : 0 ≤ d2709 p :=
  nonnegative_ite (p 224) (nonnegative2708 p) (nonnegative2707 p)
def d2710 (p : Pattern) : Int := if p 204 then d12 p else d2709 p
theorem agree2710 (p q : Pattern) (h : Agree support p q) : d2710 p = d2710 q := by
  simp only [d2710, h 204 (by decide), agree12 p q h, agree2709 p q h]
theorem nonnegative2710 (p : Pattern) : 0 ≤ d2710 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2709 p)
def d2711 (p : Pattern) : Int := if p 182 then d2710 p else d2686 p
theorem agree2711 (p q : Pattern) (h : Agree support p q) : d2711 p = d2711 q := by
  simp only [d2711, h 182 (by decide), agree2710 p q h, agree2686 p q h]
theorem nonnegative2711 (p : Pattern) : 0 ≤ d2711 p :=
  nonnegative_ite (p 182) (nonnegative2710 p) (nonnegative2686 p)
def d2712 (p : Pattern) : Int := if p 163 then d2711 p else d2706 p
theorem agree2712 (p q : Pattern) (h : Agree support p q) : d2712 p = d2712 q := by
  simp only [d2712, h 163 (by decide), agree2711 p q h, agree2706 p q h]
theorem nonnegative2712 (p : Pattern) : 0 ≤ d2712 p :=
  nonnegative_ite (p 163) (nonnegative2711 p) (nonnegative2706 p)
def d2713 (p : Pattern) : Int := if p 182 then d12 p else d2686 p
theorem agree2713 (p q : Pattern) (h : Agree support p q) : d2713 p = d2713 q := by
  simp only [d2713, h 182 (by decide), agree12 p q h, agree2686 p q h]
theorem nonnegative2713 (p : Pattern) : 0 ≤ d2713 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2686 p)
def d2714 (p : Pattern) : Int := if p 182 then d12 p else d2692 p
theorem agree2714 (p q : Pattern) (h : Agree support p q) : d2714 p = d2714 q := by
  simp only [d2714, h 182 (by decide), agree12 p q h, agree2692 p q h]
theorem nonnegative2714 (p : Pattern) : 0 ≤ d2714 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2692 p)
def d2715 (p : Pattern) : Int := if p 163 then d2714 p else d2713 p
theorem agree2715 (p q : Pattern) (h : Agree support p q) : d2715 p = d2715 q := by
  simp only [d2715, h 163 (by decide), agree2714 p q h, agree2713 p q h]
theorem nonnegative2715 (p : Pattern) : 0 ≤ d2715 p :=
  nonnegative_ite (p 163) (nonnegative2714 p) (nonnegative2713 p)
def d2716 (p : Pattern) : Int := if p 162 then d2715 p else d2712 p
theorem agree2716 (p q : Pattern) (h : Agree support p q) : d2716 p = d2716 q := by
  simp only [d2716, h 162 (by decide), agree2715 p q h, agree2712 p q h]
theorem nonnegative2716 (p : Pattern) : 0 ≤ d2716 p :=
  nonnegative_ite (p 162) (nonnegative2715 p) (nonnegative2712 p)
def d2717 (p : Pattern) : Int := if p 163 then d12 p else d2592 p
theorem agree2717 (p q : Pattern) (h : Agree support p q) : d2717 p = d2717 q := by
  simp only [d2717, h 163 (by decide), agree12 p q h, agree2592 p q h]
theorem nonnegative2717 (p : Pattern) : 0 ≤ d2717 p :=
  nonnegative_ite (p 163) (nonnegative12 p) (nonnegative2592 p)
def d2718 (p : Pattern) : Int := if p 162 then d2717 p else d2715 p
theorem agree2718 (p q : Pattern) (h : Agree support p q) : d2718 p = d2718 q := by
  simp only [d2718, h 162 (by decide), agree2717 p q h, agree2715 p q h]
theorem nonnegative2718 (p : Pattern) : 0 ≤ d2718 p :=
  nonnegative_ite (p 162) (nonnegative2717 p) (nonnegative2715 p)
def d2719 (p : Pattern) : Int := if p 161 then d2718 p else d2716 p
theorem agree2719 (p q : Pattern) (h : Agree support p q) : d2719 p = d2719 q := by
  simp only [d2719, h 161 (by decide), agree2718 p q h, agree2716 p q h]
theorem nonnegative2719 (p : Pattern) : 0 ≤ d2719 p :=
  nonnegative_ite (p 161) (nonnegative2718 p) (nonnegative2716 p)
def d2720 (p : Pattern) : Int := if p 160 then d2719 p else d2701 p
theorem agree2720 (p q : Pattern) (h : Agree support p q) : d2720 p = d2720 q := by
  simp only [d2720, h 160 (by decide), agree2719 p q h, agree2701 p q h]
theorem nonnegative2720 (p : Pattern) : 0 ≤ d2720 p :=
  nonnegative_ite (p 160) (nonnegative2719 p) (nonnegative2701 p)
def d2721 (p : Pattern) : Int := if p 225 then d327 p else d103 p
theorem agree2721 (p q : Pattern) (h : Agree support p q) : d2721 p = d2721 q := by
  simp only [d2721, h 225 (by decide), agree327 p q h, agree103 p q h]
theorem nonnegative2721 (p : Pattern) : 0 ≤ d2721 p :=
  nonnegative_ite (p 225) (nonnegative327 p) (nonnegative103 p)
def d2722 (p : Pattern) : Int := if p 224 then d2677 p else d2721 p
theorem agree2722 (p q : Pattern) (h : Agree support p q) : d2722 p = d2722 q := by
  simp only [d2722, h 224 (by decide), agree2677 p q h, agree2721 p q h]
theorem nonnegative2722 (p : Pattern) : 0 ≤ d2722 p :=
  nonnegative_ite (p 224) (nonnegative2677 p) (nonnegative2721 p)
def d2723 (p : Pattern) : Int := if p 204 then d2680 p else d2722 p
theorem agree2723 (p q : Pattern) (h : Agree support p q) : d2723 p = d2723 q := by
  simp only [d2723, h 204 (by decide), agree2680 p q h, agree2722 p q h]
theorem nonnegative2723 (p : Pattern) : 0 ≤ d2723 p :=
  nonnegative_ite (p 204) (nonnegative2680 p) (nonnegative2722 p)
def d2724 (p : Pattern) : Int := if p 182 then d2684 p else d2723 p
theorem agree2724 (p q : Pattern) (h : Agree support p q) : d2724 p = d2724 q := by
  simp only [d2724, h 182 (by decide), agree2684 p q h, agree2723 p q h]
theorem nonnegative2724 (p : Pattern) : 0 ≤ d2724 p :=
  nonnegative_ite (p 182) (nonnegative2684 p) (nonnegative2723 p)
def d2725 (p : Pattern) : Int := if p 204 then d2704 p else d2702 p
theorem agree2725 (p q : Pattern) (h : Agree support p q) : d2725 p = d2725 q := by
  simp only [d2725, h 204 (by decide), agree2704 p q h, agree2702 p q h]
theorem nonnegative2725 (p : Pattern) : 0 ≤ d2725 p :=
  nonnegative_ite (p 204) (nonnegative2704 p) (nonnegative2702 p)
def d2726 (p : Pattern) : Int := if p 225 then d12 p else d1919 p
theorem agree2726 (p q : Pattern) (h : Agree support p q) : d2726 p = d2726 q := by
  simp only [d2726, h 225 (by decide), agree12 p q h, agree1919 p q h]
theorem nonnegative2726 (p : Pattern) : 0 ≤ d2726 p :=
  nonnegative_ite (p 225) (nonnegative12 p) (nonnegative1919 p)
def d2727 (p : Pattern) : Int := if p 224 then d2726 p else d2702 p
theorem agree2727 (p q : Pattern) (h : Agree support p q) : d2727 p = d2727 q := by
  simp only [d2727, h 224 (by decide), agree2726 p q h, agree2702 p q h]
theorem nonnegative2727 (p : Pattern) : 0 ≤ d2727 p :=
  nonnegative_ite (p 224) (nonnegative2726 p) (nonnegative2702 p)
def d2728 (p : Pattern) : Int := if p 204 then d12 p else d2727 p
theorem agree2728 (p q : Pattern) (h : Agree support p q) : d2728 p = d2728 q := by
  simp only [d2728, h 204 (by decide), agree12 p q h, agree2727 p q h]
theorem nonnegative2728 (p : Pattern) : 0 ≤ d2728 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2727 p)
def d2729 (p : Pattern) : Int := if p 182 then d2728 p else d2725 p
theorem agree2729 (p q : Pattern) (h : Agree support p q) : d2729 p = d2729 q := by
  simp only [d2729, h 182 (by decide), agree2728 p q h, agree2725 p q h]
theorem nonnegative2729 (p : Pattern) : 0 ≤ d2729 p :=
  nonnegative_ite (p 182) (nonnegative2728 p) (nonnegative2725 p)
def d2730 (p : Pattern) : Int := if p 163 then d2729 p else d2724 p
theorem agree2730 (p q : Pattern) (h : Agree support p q) : d2730 p = d2730 q := by
  simp only [d2730, h 163 (by decide), agree2729 p q h, agree2724 p q h]
theorem nonnegative2730 (p : Pattern) : 0 ≤ d2730 p :=
  nonnegative_ite (p 163) (nonnegative2729 p) (nonnegative2724 p)
def d2731 (p : Pattern) : Int := if p 163 then d2581 p else d2696 p
theorem agree2731 (p q : Pattern) (h : Agree support p q) : d2731 p = d2731 q := by
  simp only [d2731, h 163 (by decide), agree2581 p q h, agree2696 p q h]
theorem nonnegative2731 (p : Pattern) : 0 ≤ d2731 p :=
  nonnegative_ite (p 163) (nonnegative2581 p) (nonnegative2696 p)
def d2732 (p : Pattern) : Int := if p 162 then d2731 p else d2730 p
theorem agree2732 (p q : Pattern) (h : Agree support p q) : d2732 p = d2732 q := by
  simp only [d2732, h 162 (by decide), agree2731 p q h, agree2730 p q h]
theorem nonnegative2732 (p : Pattern) : 0 ≤ d2732 p :=
  nonnegative_ite (p 162) (nonnegative2731 p) (nonnegative2730 p)
def d2733 (p : Pattern) : Int := if p 163 then d2584 p else d2696 p
theorem agree2733 (p q : Pattern) (h : Agree support p q) : d2733 p = d2733 q := by
  simp only [d2733, h 163 (by decide), agree2584 p q h, agree2696 p q h]
theorem nonnegative2733 (p : Pattern) : 0 ≤ d2733 p :=
  nonnegative_ite (p 163) (nonnegative2584 p) (nonnegative2696 p)
def d2734 (p : Pattern) : Int := if p 162 then d12 p else d2733 p
theorem agree2734 (p q : Pattern) (h : Agree support p q) : d2734 p = d2734 q := by
  simp only [d2734, h 162 (by decide), agree12 p q h, agree2733 p q h]
theorem nonnegative2734 (p : Pattern) : 0 ≤ d2734 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2733 p)
def d2735 (p : Pattern) : Int := if p 161 then d2734 p else d2732 p
theorem agree2735 (p q : Pattern) (h : Agree support p q) : d2735 p = d2735 q := by
  simp only [d2735, h 161 (by decide), agree2734 p q h, agree2732 p q h]
theorem nonnegative2735 (p : Pattern) : 0 ≤ d2735 p :=
  nonnegative_ite (p 161) (nonnegative2734 p) (nonnegative2732 p)
def d2736 (p : Pattern) : Int := if p 182 then d12 p else d2725 p
theorem agree2736 (p q : Pattern) (h : Agree support p q) : d2736 p = d2736 q := by
  simp only [d2736, h 182 (by decide), agree12 p q h, agree2725 p q h]
theorem nonnegative2736 (p : Pattern) : 0 ≤ d2736 p :=
  nonnegative_ite (p 182) (nonnegative12 p) (nonnegative2725 p)
def d2737 (p : Pattern) : Int := if p 163 then d2736 p else d2711 p
theorem agree2737 (p q : Pattern) (h : Agree support p q) : d2737 p = d2737 q := by
  simp only [d2737, h 163 (by decide), agree2736 p q h, agree2711 p q h]
theorem nonnegative2737 (p : Pattern) : 0 ≤ d2737 p :=
  nonnegative_ite (p 163) (nonnegative2736 p) (nonnegative2711 p)
def d2738 (p : Pattern) : Int := if p 163 then d2592 p else d2714 p
theorem agree2738 (p q : Pattern) (h : Agree support p q) : d2738 p = d2738 q := by
  simp only [d2738, h 163 (by decide), agree2592 p q h, agree2714 p q h]
theorem nonnegative2738 (p : Pattern) : 0 ≤ d2738 p :=
  nonnegative_ite (p 163) (nonnegative2592 p) (nonnegative2714 p)
def d2739 (p : Pattern) : Int := if p 162 then d2738 p else d2737 p
theorem agree2739 (p q : Pattern) (h : Agree support p q) : d2739 p = d2739 q := by
  simp only [d2739, h 162 (by decide), agree2738 p q h, agree2737 p q h]
theorem nonnegative2739 (p : Pattern) : 0 ≤ d2739 p :=
  nonnegative_ite (p 162) (nonnegative2738 p) (nonnegative2737 p)
def d2740 (p : Pattern) : Int := if p 163 then d2594 p else d2714 p
theorem agree2740 (p q : Pattern) (h : Agree support p q) : d2740 p = d2740 q := by
  simp only [d2740, h 163 (by decide), agree2594 p q h, agree2714 p q h]
theorem nonnegative2740 (p : Pattern) : 0 ≤ d2740 p :=
  nonnegative_ite (p 163) (nonnegative2594 p) (nonnegative2714 p)
def d2741 (p : Pattern) : Int := if p 162 then d12 p else d2740 p
theorem agree2741 (p q : Pattern) (h : Agree support p q) : d2741 p = d2741 q := by
  simp only [d2741, h 162 (by decide), agree12 p q h, agree2740 p q h]
theorem nonnegative2741 (p : Pattern) : 0 ≤ d2741 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2740 p)
def d2742 (p : Pattern) : Int := if p 161 then d2741 p else d2739 p
theorem agree2742 (p q : Pattern) (h : Agree support p q) : d2742 p = d2742 q := by
  simp only [d2742, h 161 (by decide), agree2741 p q h, agree2739 p q h]
theorem nonnegative2742 (p : Pattern) : 0 ≤ d2742 p :=
  nonnegative_ite (p 161) (nonnegative2741 p) (nonnegative2739 p)
def d2743 (p : Pattern) : Int := if p 160 then d2742 p else d2735 p
theorem agree2743 (p q : Pattern) (h : Agree support p q) : d2743 p = d2743 q := by
  simp only [d2743, h 160 (by decide), agree2742 p q h, agree2735 p q h]
theorem nonnegative2743 (p : Pattern) : 0 ≤ d2743 p :=
  nonnegative_ite (p 160) (nonnegative2742 p) (nonnegative2735 p)
def d2744 (p : Pattern) : Int := if p 141 then d2743 p else d2720 p
theorem agree2744 (p q : Pattern) (h : Agree support p q) : d2744 p = d2744 q := by
  simp only [d2744, h 141 (by decide), agree2743 p q h, agree2720 p q h]
theorem nonnegative2744 (p : Pattern) : 0 ≤ d2744 p :=
  nonnegative_ite (p 141) (nonnegative2743 p) (nonnegative2720 p)
def d2745 (p : Pattern) : Int := if p 204 then d12 p else d2680 p
theorem agree2745 (p q : Pattern) (h : Agree support p q) : d2745 p = d2745 q := by
  simp only [d2745, h 204 (by decide), agree12 p q h, agree2680 p q h]
theorem nonnegative2745 (p : Pattern) : 0 ≤ d2745 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2680 p)
def d2746 (p : Pattern) : Int := if p 182 then d2745 p else d2686 p
theorem agree2746 (p q : Pattern) (h : Agree support p q) : d2746 p = d2746 q := by
  simp only [d2746, h 182 (by decide), agree2745 p q h, agree2686 p q h]
theorem nonnegative2746 (p : Pattern) : 0 ≤ d2746 p :=
  nonnegative_ite (p 182) (nonnegative2745 p) (nonnegative2686 p)
def d2747 (p : Pattern) : Int := if p 204 then d12 p else d2691 p
theorem agree2747 (p q : Pattern) (h : Agree support p q) : d2747 p = d2747 q := by
  simp only [d2747, h 204 (by decide), agree12 p q h, agree2691 p q h]
theorem nonnegative2747 (p : Pattern) : 0 ≤ d2747 p :=
  nonnegative_ite (p 204) (nonnegative12 p) (nonnegative2691 p)
def d2748 (p : Pattern) : Int := if p 182 then d2747 p else d2692 p
theorem agree2748 (p q : Pattern) (h : Agree support p q) : d2748 p = d2748 q := by
  simp only [d2748, h 182 (by decide), agree2747 p q h, agree2692 p q h]
theorem nonnegative2748 (p : Pattern) : 0 ≤ d2748 p :=
  nonnegative_ite (p 182) (nonnegative2747 p) (nonnegative2692 p)
def d2749 (p : Pattern) : Int := if p 163 then d2748 p else d2746 p
theorem agree2749 (p q : Pattern) (h : Agree support p q) : d2749 p = d2749 q := by
  simp only [d2749, h 163 (by decide), agree2748 p q h, agree2746 p q h]
theorem nonnegative2749 (p : Pattern) : 0 ≤ d2749 p :=
  nonnegative_ite (p 163) (nonnegative2748 p) (nonnegative2746 p)
def d2750 (p : Pattern) : Int := if p 162 then d2749 p else d2746 p
theorem agree2750 (p q : Pattern) (h : Agree support p q) : d2750 p = d2750 q := by
  simp only [d2750, h 162 (by decide), agree2749 p q h, agree2746 p q h]
theorem nonnegative2750 (p : Pattern) : 0 ≤ d2750 p :=
  nonnegative_ite (p 162) (nonnegative2749 p) (nonnegative2746 p)
def d2751 (p : Pattern) : Int := if p 162 then d2699 p else d2749 p
theorem agree2751 (p q : Pattern) (h : Agree support p q) : d2751 p = d2751 q := by
  simp only [d2751, h 162 (by decide), agree2699 p q h, agree2749 p q h]
theorem nonnegative2751 (p : Pattern) : 0 ≤ d2751 p :=
  nonnegative_ite (p 162) (nonnegative2699 p) (nonnegative2749 p)
def d2752 (p : Pattern) : Int := if p 161 then d2751 p else d2750 p
theorem agree2752 (p q : Pattern) (h : Agree support p q) : d2752 p = d2752 q := by
  simp only [d2752, h 161 (by decide), agree2751 p q h, agree2750 p q h]
theorem nonnegative2752 (p : Pattern) : 0 ≤ d2752 p :=
  nonnegative_ite (p 161) (nonnegative2751 p) (nonnegative2750 p)
def d2753 (p : Pattern) : Int := if p 182 then d2705 p else d2725 p
theorem agree2753 (p q : Pattern) (h : Agree support p q) : d2753 p = d2753 q := by
  simp only [d2753, h 182 (by decide), agree2705 p q h, agree2725 p q h]
theorem nonnegative2753 (p : Pattern) : 0 ≤ d2753 p :=
  nonnegative_ite (p 182) (nonnegative2705 p) (nonnegative2725 p)
def d2754 (p : Pattern) : Int := if p 204 then d2709 p else d2707 p
theorem agree2754 (p q : Pattern) (h : Agree support p q) : d2754 p = d2754 q := by
  simp only [d2754, h 204 (by decide), agree2709 p q h, agree2707 p q h]
theorem nonnegative2754 (p : Pattern) : 0 ≤ d2754 p :=
  nonnegative_ite (p 204) (nonnegative2709 p) (nonnegative2707 p)
def d2755 (p : Pattern) : Int := if p 182 then d2710 p else d2754 p
theorem agree2755 (p q : Pattern) (h : Agree support p q) : d2755 p = d2755 q := by
  simp only [d2755, h 182 (by decide), agree2710 p q h, agree2754 p q h]
theorem nonnegative2755 (p : Pattern) : 0 ≤ d2755 p :=
  nonnegative_ite (p 182) (nonnegative2710 p) (nonnegative2754 p)
def d2756 (p : Pattern) : Int := if p 163 then d2755 p else d2753 p
theorem agree2756 (p q : Pattern) (h : Agree support p q) : d2756 p = d2756 q := by
  simp only [d2756, h 163 (by decide), agree2755 p q h, agree2753 p q h]
theorem nonnegative2756 (p : Pattern) : 0 ≤ d2756 p :=
  nonnegative_ite (p 163) (nonnegative2755 p) (nonnegative2753 p)
def d2757 (p : Pattern) : Int := if p 162 then d12 p else d2756 p
theorem agree2757 (p q : Pattern) (h : Agree support p q) : d2757 p = d2757 q := by
  simp only [d2757, h 162 (by decide), agree12 p q h, agree2756 p q h]
theorem nonnegative2757 (p : Pattern) : 0 ≤ d2757 p :=
  nonnegative_ite (p 162) (nonnegative12 p) (nonnegative2756 p)
def d2758 (p : Pattern) : Int := if p 161 then d12 p else d2757 p
theorem agree2758 (p q : Pattern) (h : Agree support p q) : d2758 p = d2758 q := by
  simp only [d2758, h 161 (by decide), agree12 p q h, agree2757 p q h]
theorem nonnegative2758 (p : Pattern) : 0 ≤ d2758 p :=
  nonnegative_ite (p 161) (nonnegative12 p) (nonnegative2757 p)
def d2759 (p : Pattern) : Int := if p 160 then d2758 p else d2752 p
theorem agree2759 (p q : Pattern) (h : Agree support p q) : d2759 p = d2759 q := by
  simp only [d2759, h 160 (by decide), agree2758 p q h, agree2752 p q h]
theorem nonnegative2759 (p : Pattern) : 0 ≤ d2759 p :=
  nonnegative_ite (p 160) (nonnegative2758 p) (nonnegative2752 p)
end NetHack.Sokoban22Refined85
