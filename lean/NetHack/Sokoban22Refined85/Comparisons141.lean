/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons140
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare19740 (p : Pattern) (guard : d5540 p = 1) : d2425 p ≤ (0 : Int) + d5762 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2425, d5762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19738 p hg
    simpa only [d2425, d5762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2425, d5762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2425, d5762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19741 (p : Pattern) (guard : d5540 p = 1) : d2426 p ≤ (0 : Int) + d5763 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2426, d5763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19739 p hg
    simpa only [d2426, d5763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2426, d5763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19740 p hg
    simpa only [d2426, d5763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19742 (p : Pattern) (guard : d5540 p = 1) : d2427 p ≤ (0 : Int) + d5764 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2427, d5764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19512 p hg
    simpa only [d2427, d5764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2427, d5764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19741 p hg
    simpa only [d2427, d5764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19743 (p : Pattern) (guard : d5540 p = 1) : d2428 p ≤ (0 : Int) + d5765 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2428, d5765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19742 p hg
    simpa only [d2428, d5765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2428, d5765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2428, d5765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19744 (p : Pattern) (guard : d5540 p = 1) : d2429 p ≤ (0 : Int) + d5766 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2429, d5766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19743 p hg
    simpa only [d2429, d5766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2429, d5766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2429, d5766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19745 (p : Pattern) (guard : d5540 p = 1) : d2430 p ≤ (0 : Int) + d5767 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2430, d5767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19734 p hg
    simpa only [d2430, d5767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2430, d5767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19744 p hg
    simpa only [d2430, d5767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19746 (p : Pattern) (guard : d5540 p = 1) : d2431 p ≤ (0 : Int) + d5768 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2431, d5768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19512 p hg
    simpa only [d2431, d5768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2431, d5768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19493 p hg
    simpa only [d2431, d5768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19747 (p : Pattern) (guard : d5540 p = 1) : d2432 p ≤ (0 : Int) + d5769 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2432, d5769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19520 p hg
    simpa only [d2432, d5769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2432, d5769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19746 p hg
    simpa only [d2432, d5769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19748 (p : Pattern) (guard : d5540 p = 1) : d2433 p ≤ (0 : Int) + d5770 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2433, d5770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19747 p hg
    simpa only [d2433, d5770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2433, d5770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19535 p hg
    simpa only [d2433, d5770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19749 (p : Pattern) (guard : d5540 p = 1) : d2434 p ≤ (0 : Int) + d5771 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2434, d5771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19741 p hg
    simpa only [d2434, d5771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2434, d5771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2434, d5771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19750 (p : Pattern) (guard : d5540 p = 1) : d2435 p ≤ (0 : Int) + d5772 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2435, d5772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19749 p hg
    simpa only [d2435, d5772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2435, d5772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2435, d5772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19751 (p : Pattern) (guard : d5540 p = 1) : d2436 p ≤ (0 : Int) + d5773 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2436, d5773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19750 p hg
    simpa only [d2436, d5773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2436, d5773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2436, d5773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19752 (p : Pattern) (guard : d5540 p = 1) : d2437 p ≤ (0 : Int) + d5774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2437, d5774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19748 p hg
    simpa only [d2437, d5774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2437, d5774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19751 p hg
    simpa only [d2437, d5774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19753 (p : Pattern) (guard : d5540 p = 1) : d2438 p ≤ (0 : Int) + d5775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2438, d5775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19745 p hg
    simpa only [d2438, d5775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2438, d5775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19752 p hg
    simpa only [d2438, d5775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19754 (p : Pattern) (guard : d5540 p = 1) : d2439 p ≤ (0 : Int) + d5776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2439, d5776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19732 p hg
    simpa only [d2439, d5776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2439, d5776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19753 p hg
    simpa only [d2439, d5776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19755 (p : Pattern) (guard : d5540 p = 1) : d2440 p ≤ (0 : Int) + d5777 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2440, d5777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19753 p hg
    simpa only [d2440, d5777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2440, d5777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2440, d5777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19756 (p : Pattern) (guard : d5540 p = 1) : d2441 p ≤ (0 : Int) + d5778 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2441, d5778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19754 p hg
    simpa only [d2441, d5778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2441, d5778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19755 p hg
    simpa only [d2441, d5778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19757 (p : Pattern) (guard : d5540 p = 1) : d2442 p ≤ (0 : Int) + d5779 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2442, d5779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19583 p hg
    simpa only [d2442, d5779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2442, d5779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19756 p hg
    simpa only [d2442, d5779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19758 (p : Pattern) (guard : d5540 p = 1) : d2443 p ≤ (0 : Int) + d5780 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2443, d5780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19568 p hg
    simpa only [d2443, d5780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2443, d5780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19757 p hg
    simpa only [d2443, d5780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19759 (p : Pattern) (guard : d5540 p = 1) : d2444 p ≤ (0 : Int) + d5781 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2444, d5781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19617 p hg
    simpa only [d2444, d5781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2444, d5781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2444, d5781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19760 (p : Pattern) (guard : d5540 p = 1) : d2445 p ≤ (0 : Int) + d5782 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2445, d5782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19651 p hg
    simpa only [d2445, d5782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2445, d5782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19759 p hg
    simpa only [d2445, d5782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19761 (p : Pattern) (guard : d5540 p = 1) : d2446 p ≤ (0 : Int) + d5783 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2446, d5783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19759 p hg
    simpa only [d2446, d5783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2446, d5783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2446, d5783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19762 (p : Pattern) (guard : d5540 p = 1) : d2447 p ≤ (0 : Int) + d5784 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2447, d5784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19760 p hg
    simpa only [d2447, d5784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2447, d5784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19761 p hg
    simpa only [d2447, d5784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19763 (p : Pattern) (guard : d5540 p = 1) : d2448 p ≤ (0 : Int) + d5785 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2448, d5785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19635 p hg
    simpa only [d2448, d5785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2448, d5785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2448, d5785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19764 (p : Pattern) (guard : d5540 p = 1) : d2449 p ≤ (0 : Int) + d5786 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2449, d5786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19658 p hg
    simpa only [d2449, d5786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2449, d5786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19763 p hg
    simpa only [d2449, d5786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19765 (p : Pattern) (guard : d5540 p = 1) : d2450 p ≤ (0 : Int) + d5787 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2450, d5787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19763 p hg
    simpa only [d2450, d5787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2450, d5787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2450, d5787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19766 (p : Pattern) (guard : d5540 p = 1) : d2451 p ≤ (0 : Int) + d5788 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2451, d5788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19764 p hg
    simpa only [d2451, d5788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2451, d5788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19765 p hg
    simpa only [d2451, d5788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19767 (p : Pattern) (guard : d5540 p = 1) : d2452 p ≤ (0 : Int) + d5789 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2452, d5789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19762 p hg
    simpa only [d2452, d5789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2452, d5789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19766 p hg
    simpa only [d2452, d5789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19768 (p : Pattern) (guard : d5540 p = 1) : d2453 p ≤ (0 : Int) + d5790 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2453, d5790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19641 p hg
    simpa only [d2453, d5790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2453, d5790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19767 p hg
    simpa only [d2453, d5790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19769 (p : Pattern) (guard : d5540 p = 1) : d2444 p ≤ (0 : Int) + d5791 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2444, d5791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19669 p hg
    simpa only [d2444, d5791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2444, d5791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2444, d5791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19770 (p : Pattern) (guard : d5540 p = 1) : d2454 p ≤ (0 : Int) + d5792 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2454, d5792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19682 p hg
    simpa only [d2454, d5792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2454, d5792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19769 p hg
    simpa only [d2454, d5792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19771 (p : Pattern) (guard : d5540 p = 1) : d2446 p ≤ (0 : Int) + d5793 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2446, d5793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19769 p hg
    simpa only [d2446, d5793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2446, d5793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2446, d5793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19772 (p : Pattern) (guard : d5540 p = 1) : d2455 p ≤ (0 : Int) + d5794 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2455, d5794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19770 p hg
    simpa only [d2455, d5794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2455, d5794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19771 p hg
    simpa only [d2455, d5794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19773 (p : Pattern) (guard : d5540 p = 1) : d2456 p ≤ (0 : Int) + d5795 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2456, d5795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19772 p hg
    simpa only [d2456, d5795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2456, d5795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19690 p hg
    simpa only [d2456, d5795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19774 (p : Pattern) (guard : d5540 p = 1) : d2457 p ≤ (0 : Int) + d5796 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2457, d5796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19681 p hg
    simpa only [d2457, d5796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2457, d5796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19773 p hg
    simpa only [d2457, d5796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19775 (p : Pattern) (guard : d5540 p = 1) : d2458 p ≤ (0 : Int) + d5797 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2458, d5797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19768 p hg
    simpa only [d2458, d5797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2458, d5797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19774 p hg
    simpa only [d2458, d5797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19776 (p : Pattern) (guard : d5540 p = 1) : d2459 p ≤ (0 : Int) + d5798 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2459, d5798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19774 p hg
    simpa only [d2459, d5798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2459, d5798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19697 p hg
    simpa only [d2459, d5798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19777 (p : Pattern) (guard : d5540 p = 1) : d2460 p ≤ (0 : Int) + d5799 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2460, d5799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19775 p hg
    simpa only [d2460, d5799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2460, d5799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19776 p hg
    simpa only [d2460, d5799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19778 (p : Pattern) (guard : d5540 p = 1) : d2325 p ≤ (0 : Int) + d5703 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2325, d5703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19603 p hg
    simpa only [d2325, d5703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2325, d5703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19666 p hg
    simpa only [d2325, d5703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19779 (p : Pattern) (guard : d5540 p = 1) : d2392 p ≤ (0 : Int) + d5703 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19778 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19667 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19780 (p : Pattern) (guard : d5540 p = 1) : d2393 p ≤ (0 : Int) + d5707 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2393, d5707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19779 p hg
    simpa only [d2393, d5707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2393, d5707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19670 p hg
    simpa only [d2393, d5707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19781 (p : Pattern) (guard : d5540 p = 1) : d2394 p ≤ (0 : Int) + d5709 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2394, d5709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19780 p hg
    simpa only [d2394, d5709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2394, d5709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19672 p hg
    simpa only [d2394, d5709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19782 (p : Pattern) (guard : d5540 p = 1) : d2461 p ≤ (0 : Int) + d5800 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2461, d5800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19646 p hg
    simpa only [d2461, d5800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2461, d5800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19631 p hg
    simpa only [d2461, d5800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19783 (p : Pattern) (guard : d5540 p = 1) : d2462 p ≤ (0 : Int) + d5801 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2462, d5801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19674 p hg
    simpa only [d2462, d5801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2462, d5801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19782 p hg
    simpa only [d2462, d5801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19784 (p : Pattern) (guard : d5540 p = 1) : d2463 p ≤ (0 : Int) + d5802 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2463, d5802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19783 p hg
    simpa only [d2463, d5802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2463, d5802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19763 p hg
    simpa only [d2463, d5802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19785 (p : Pattern) (guard : d5540 p = 1) : d2464 p ≤ (0 : Int) + d5803 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2464, d5803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19676 p hg
    simpa only [d2464, d5803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2464, d5803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2464, d5803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19786 (p : Pattern) (guard : d5540 p = 1) : d2465 p ≤ (0 : Int) + d5804 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2465, d5804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19785 p hg
    simpa only [d2465, d5804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2465, d5804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2465, d5804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19787 (p : Pattern) (guard : d5540 p = 1) : d2466 p ≤ (0 : Int) + d5805 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2466, d5805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19786 p hg
    simpa only [d2466, d5805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2466, d5805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2466, d5805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19788 (p : Pattern) (guard : d5540 p = 1) : d2467 p ≤ (0 : Int) + d5806 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2467, d5806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19784 p hg
    simpa only [d2467, d5806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2467, d5806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19787 p hg
    simpa only [d2467, d5806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19789 (p : Pattern) (guard : d5540 p = 1) : d2468 p ≤ (0 : Int) + d5807 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2468, d5807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19781 p hg
    simpa only [d2468, d5807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2468, d5807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19788 p hg
    simpa only [d2468, d5807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19790 (p : Pattern) (guard : d5540 p = 1) : d2469 p ≤ (0 : Int) + d5808 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2469, d5808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19613 p hg
    simpa only [d2469, d5808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2469, d5808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19631 p hg
    simpa only [d2469, d5808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19791 (p : Pattern) (guard : d5540 p = 1) : d2470 p ≤ (0 : Int) + d5809 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2470, d5809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19790 p hg
    simpa only [d2470, d5809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2470, d5809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19635 p hg
    simpa only [d2470, d5809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19792 (p : Pattern) (guard : d5540 p = 1) : d2471 p ≤ (0 : Int) + d5810 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2471, d5810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19791 p hg
    simpa only [d2471, d5810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2471, d5810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19786 p hg
    simpa only [d2471, d5810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19793 (p : Pattern) (guard : d5540 p = 1) : d2472 p ≤ (0 : Int) + d5811 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2472, d5811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19467 p hg
    simpa only [d2472, d5811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2472, d5811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2472, d5811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19794 (p : Pattern) (guard : d5540 p = 1) : d2473 p ≤ (0 : Int) + d5812 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2473, d5812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19792 p hg
    simpa only [d2473, d5812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2473, d5812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19793 p hg
    simpa only [d2473, d5812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19795 (p : Pattern) (guard : d5540 p = 1) : d2474 p ≤ (0 : Int) + d5813 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2474, d5813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19772 p hg
    simpa only [d2474, d5813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2474, d5813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19794 p hg
    simpa only [d2474, d5813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19796 (p : Pattern) (guard : d5540 p = 1) : d2475 p ≤ (0 : Int) + d5814 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2475, d5814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19789 p hg
    simpa only [d2475, d5814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2475, d5814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19795 p hg
    simpa only [d2475, d5814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19797 (p : Pattern) (guard : d5540 p = 1) : d2476 p ≤ (0 : Int) + d5815 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2476, d5815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19674 p hg
    simpa only [d2476, d5815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2476, d5815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19493 p hg
    simpa only [d2476, d5815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19798 (p : Pattern) (guard : d5540 p = 1) : d2477 p ≤ (0 : Int) + d5816 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2477, d5816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19667 p hg
    simpa only [d2477, d5816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2477, d5816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19797 p hg
    simpa only [d2477, d5816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19799 (p : Pattern) (guard : d5540 p = 1) : d2478 p ≤ (0 : Int) + d5817 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2478, d5817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19798 p hg
    simpa only [d2478, d5817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2478, d5817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19686 p hg
    simpa only [d2478, d5817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19800 (p : Pattern) (guard : d5540 p = 1) : d2479 p ≤ (0 : Int) + d5818 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2479, d5818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19799 p hg
    simpa only [d2479, d5818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2479, d5818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19690 p hg
    simpa only [d2479, d5818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19801 (p : Pattern) (guard : d5540 p = 1) : d2480 p ≤ (0 : Int) + d5819 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2480, d5819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19674 p hg
    simpa only [d2480, d5819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2480, d5819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19769 p hg
    simpa only [d2480, d5819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19802 (p : Pattern) (guard : d5540 p = 1) : d2481 p ≤ (0 : Int) + d5820 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2481, d5820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19801 p hg
    simpa only [d2481, d5820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2481, d5820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19689 p hg
    simpa only [d2481, d5820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19803 (p : Pattern) (guard : d5540 p = 1) : d2482 p ≤ (0 : Int) + d5821 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2482, d5821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19517 p hg
    simpa only [d2482, d5821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2482, d5821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2482, d5821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19804 (p : Pattern) (guard : d5540 p = 1) : d2483 p ≤ (0 : Int) + d5822 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2483, d5822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19803 p hg
    simpa only [d2483, d5822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2483, d5822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2483, d5822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19805 (p : Pattern) (guard : d5540 p = 1) : d2484 p ≤ (0 : Int) + d5823 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2484, d5823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19802 p hg
    simpa only [d2484, d5823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2484, d5823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19804 p hg
    simpa only [d2484, d5823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19806 (p : Pattern) (guard : d5540 p = 1) : d2485 p ≤ (0 : Int) + d5824 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2485, d5824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19800 p hg
    simpa only [d2485, d5824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2485, d5824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19805 p hg
    simpa only [d2485, d5824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19807 (p : Pattern) (guard : d5540 p = 1) : d2486 p ≤ (0 : Int) + d5825 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2486, d5825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19796 p hg
    simpa only [d2486, d5825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2486, d5825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19806 p hg
    simpa only [d2486, d5825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19808 (p : Pattern) (guard : d5540 p = 1) : d2487 p ≤ (0 : Int) + d5826 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2487, d5826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19674 p hg
    simpa only [d2487, d5826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2487, d5826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19516 p hg
    simpa only [d2487, d5826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19809 (p : Pattern) (guard : d5540 p = 1) : d2488 p ≤ (0 : Int) + d5827 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2488, d5827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19667 p hg
    simpa only [d2488, d5827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2488, d5827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19808 p hg
    simpa only [d2488, d5827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19810 (p : Pattern) (guard : d5540 p = 1) : d2489 p ≤ (0 : Int) + d5828 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2489, d5828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19669 p hg
    simpa only [d2489, d5828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2489, d5828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19516 p hg
    simpa only [d2489, d5828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19811 (p : Pattern) (guard : d5540 p = 1) : d2490 p ≤ (0 : Int) + d5829 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2490, d5829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19810 p hg
    simpa only [d2490, d5829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2490, d5829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2490, d5829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19812 (p : Pattern) (guard : d5540 p = 1) : d2491 p ≤ (0 : Int) + d5830 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2491, d5830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19809 p hg
    simpa only [d2491, d5830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2491, d5830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19811 p hg
    simpa only [d2491, d5830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19813 (p : Pattern) (guard : d5540 p = 1) : d2492 p ≤ (0 : Int) + d5831 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2492, d5831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19677 p hg
    simpa only [d2492, d5831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2492, d5831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19493 p hg
    simpa only [d2492, d5831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19814 (p : Pattern) (guard : d5540 p = 1) : d2493 p ≤ (0 : Int) + d5832 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2493, d5832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19813 p hg
    simpa only [d2493, d5832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2493, d5832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2493, d5832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19815 (p : Pattern) (guard : d5540 p = 1) : d2494 p ≤ (0 : Int) + d5833 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2494, d5833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19814 p hg
    simpa only [d2494, d5833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2494, d5833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2494, d5833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19816 (p : Pattern) (guard : d5540 p = 1) : d2495 p ≤ (0 : Int) + d5834 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2495, d5834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19812 p hg
    simpa only [d2495, d5834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2495, d5834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19815 p hg
    simpa only [d2495, d5834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19817 (p : Pattern) (guard : d5540 p = 1) : d2496 p ≤ (0 : Int) + d5835 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2496, d5835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19816 p hg
    simpa only [d2496, d5835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2496, d5835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19805 p hg
    simpa only [d2496, d5835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19818 (p : Pattern) (guard : d5540 p = 1) : d2497 p ≤ (0 : Int) + d5836 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2497, d5836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19817 p hg
    simpa only [d2497, d5836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2497, d5836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2497, d5836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19819 (p : Pattern) (guard : d5540 p = 1) : d2498 p ≤ (0 : Int) + d5837 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2498, d5837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19807 p hg
    simpa only [d2498, d5837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2498, d5837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19818 p hg
    simpa only [d2498, d5837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19820 (p : Pattern) (guard : d5540 p = 1) : d2499 p ≤ (0 : Int) + d5838 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2499, d5838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19777 p hg
    simpa only [d2499, d5838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2499, d5838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19819 p hg
    simpa only [d2499, d5838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19821 (p : Pattern) (guard : d5540 p = 1) : d2500 p ≤ (0 : Int) + d5839 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2500, d5839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19568 p hg
    simpa only [d2500, d5839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2500, d5839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19820 p hg
    simpa only [d2500, d5839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19822 (p : Pattern) (guard : d5540 p = 1) : d2501 p ≤ (0 : Int) + d5840 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2501, d5840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19758 p hg
    simpa only [d2501, d5840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2501, d5840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19821 p hg
    simpa only [d2501, d5840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19823 (p : Pattern) (guard : d5540 p = 1) : d2502 p ≤ (0 : Int) + d5841 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2502, d5841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19714 p hg
    simpa only [d2502, d5841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2502, d5841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19822 p hg
    simpa only [d2502, d5841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19824 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19825 (p : Pattern) (guard : d5843 p = 1) : d0 p ≤ (0 : Int) + d313 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19824 p hg
    simpa only [d5843, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19826 (p : Pattern) (guard : d5843 p = 1) : d13 p ≤ (0 : Int) + d13 p := by
  omega
theorem compare19827 (p : Pattern) (guard : d5843 p = 1) : d14 p ≤ (0 : Int) + d3540 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d14, d3540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19825 p hg
    simpa only [d14, d3540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d14, d3540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19826 p hg
    simpa only [d14, d3540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19828 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19829 (p : Pattern) (guard : d5843 p = 1) : d0 p ≤ (0 : Int) + d13 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19828 p hg
    simpa only [d5843, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19830 (p : Pattern) (guard : d5847 p = 1) : d14 p ≤ (0 : Int) + d13 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19829 p hg
    simpa only [d5847, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14530 p hg
    simpa only [d5847, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19831 (p : Pattern) (guard : d5848 p = 1) : d14 p ≤ (0 : Int) + d3541 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19827 p hg
    simpa only [d5848, d3541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19830 p hg
    simpa only [d5848, d3541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19832 (p : Pattern) (guard : d0 p = 1) : d318 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19833 (p : Pattern) (guard : d5849 p = 1) : d2184 p ≤ (0 : Int) + d3542 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2184, d3542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19831 p hg
    simpa only [d5849, d2184, d3542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2184, d3542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19832 p hg
    simpa only [d5849, d2184, d3542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19834 (p : Pattern) (guard : d5843 p = 1) : d14 p ≤ (0 : Int) + d13 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19829 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19826 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19835 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d17 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19836 (p : Pattern) (guard : d5847 p = 1) : d14 p ≤ (0 : Int) + d3543 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d14, d3543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19829 p hg
    simpa only [d5847, d14, d3543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d14, d3543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19835 p hg
    simpa only [d5847, d14, d3543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19837 (p : Pattern) (guard : d5848 p = 1) : d14 p ≤ (0 : Int) + d3544 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d5848, d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19836 p hg
    simpa only [d5848, d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19838 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3543 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19839 (p : Pattern) (guard : d5849 p = 1) : d2185 p ≤ (0 : Int) + d3545 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2185, d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19837 p hg
    simpa only [d5849, d2185, d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2185, d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19838 p hg
    simpa only [d5849, d2185, d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19840 (p : Pattern) (guard : d5849 p = 1) : d2186 p ≤ (0 : Int) + d3546 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2186, d3546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19833 p hg
    simpa only [d2186, d3546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2186, d3546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19839 p hg
    simpa only [d2186, d3546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19841 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d30 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19842 (p : Pattern) (guard : d5847 p = 1) : d14 p ≤ (0 : Int) + d3547 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d14, d3547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19829 p hg
    simpa only [d5847, d14, d3547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d14, d3547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19841 p hg
    simpa only [d5847, d14, d3547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19843 (p : Pattern) (guard : d5848 p = 1) : d14 p ≤ (0 : Int) + d3548 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d5848, d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19842 p hg
    simpa only [d5848, d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19844 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3547 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19845 (p : Pattern) (guard : d5849 p = 1) : d2185 p ≤ (0 : Int) + d3549 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2185, d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19843 p hg
    simpa only [d5849, d2185, d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2185, d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19844 p hg
    simpa only [d5849, d2185, d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19846 (p : Pattern) (guard : d5849 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare19847 (p : Pattern) (guard : d5849 p = 1) : d2187 p ≤ (0 : Int) + d3550 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2187, d3550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19845 p hg
    simpa only [d2187, d3550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2187, d3550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2187, d3550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19848 (p : Pattern) (guard : d5849 p = 1) : d2188 p ≤ (0 : Int) + d3551 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2188, d3551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19840 p hg
    simpa only [d2188, d3551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2188, d3551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19847 p hg
    simpa only [d2188, d3551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19849 (p : Pattern) (guard : d5848 p = 1) : d14 p ≤ (0 : Int) + d13 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19834 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19830 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19850 (p : Pattern) (guard : d0 p = 1) : d330 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19851 (p : Pattern) (guard : d5849 p = 1) : d2189 p ≤ (0 : Int) + d13 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19849 p hg
    simpa only [d5849, d2189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19850 p hg
    simpa only [d5849, d2189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19852 (p : Pattern) (guard : d5849 p = 1) : d2190 p ≤ (0 : Int) + d3552 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2190, d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19851 p hg
    simpa only [d2190, d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2190, d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19839 p hg
    simpa only [d2190, d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19853 (p : Pattern) (guard : d5849 p = 1) : d2191 p ≤ (0 : Int) + d3553 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2191, d3553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19852 p hg
    simpa only [d2191, d3553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2191, d3553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19847 p hg
    simpa only [d2191, d3553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19854 (p : Pattern) (guard : d5849 p = 1) : d2192 p ≤ (0 : Int) + d3554 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2192, d3554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19848 p hg
    simpa only [d2192, d3554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2192, d3554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19853 p hg
    simpa only [d2192, d3554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19855 (p : Pattern) (guard : d0 p = 1) : d332 p ≤ (0 : Int) + d13 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19856 (p : Pattern) (guard : d5849 p = 1) : d2193 p ≤ (0 : Int) + d13 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19849 p hg
    simpa only [d5849, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19855 p hg
    simpa only [d5849, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19857 (p : Pattern) (guard : d5849 p = 1) : d2194 p ≤ (0 : Int) + d3552 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2194, d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19856 p hg
    simpa only [d2194, d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2194, d3552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19839 p hg
    simpa only [d2194, d3552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19858 (p : Pattern) (guard : d5849 p = 1) : d2195 p ≤ (0 : Int) + d3553 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2195, d3553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19857 p hg
    simpa only [d2195, d3553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2195, d3553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19847 p hg
    simpa only [d2195, d3553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19859 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19860 (p : Pattern) (guard : d5843 p = 1) : d4 p ≤ (0 : Int) + d17 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14537 p hg
    simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19859 p hg
    simpa only [d5843, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19861 (p : Pattern) (guard : d5843 p = 1) : d17 p ≤ (0 : Int) + d17 p := by
  omega
theorem compare19862 (p : Pattern) (guard : d5843 p = 1) : d18 p ≤ (0 : Int) + d17 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19860 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19861 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19863 (p : Pattern) (guard : d5847 p = 1) : d18 p ≤ (0 : Int) + d17 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19860 p hg
    simpa only [d5847, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14539 p hg
    simpa only [d5847, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19864 (p : Pattern) (guard : d5848 p = 1) : d18 p ≤ (0 : Int) + d17 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19862 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19863 p hg
    simpa only [d5848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19865 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d17 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19866 (p : Pattern) (guard : d5849 p = 1) : d2196 p ≤ (0 : Int) + d17 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19864 p hg
    simpa only [d5849, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19865 p hg
    simpa only [d5849, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19867 (p : Pattern) (guard : d0 p = 1) : d17 p ≤ (0 : Int) + d190 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19868 (p : Pattern) (guard : d5847 p = 1) : d18 p ≤ (0 : Int) + d3555 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d18, d3555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19860 p hg
    simpa only [d5847, d18, d3555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d18, d3555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19867 p hg
    simpa only [d5847, d18, d3555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19869 (p : Pattern) (guard : d5848 p = 1) : d18 p ≤ (0 : Int) + d3556 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19862 p hg
    simpa only [d5848, d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19868 p hg
    simpa only [d5848, d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19870 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3555 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19871 (p : Pattern) (guard : d5849 p = 1) : d2196 p ≤ (0 : Int) + d3557 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2196, d3557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19869 p hg
    simpa only [d5849, d2196, d3557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2196, d3557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19870 p hg
    simpa only [d5849, d2196, d3557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19872 (p : Pattern) (guard : d5849 p = 1) : d2196 p ≤ (0 : Int) + d3558 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19866 p hg
    simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19871 p hg
    simpa only [d3558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19873 (p : Pattern) (guard : d0 p = 1) : d17 p ≤ (0 : Int) + d34 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19874 (p : Pattern) (guard : d5847 p = 1) : d18 p ≤ (0 : Int) + d3559 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d18, d3559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19860 p hg
    simpa only [d5847, d18, d3559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d18, d3559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19873 p hg
    simpa only [d5847, d18, d3559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19875 (p : Pattern) (guard : d5848 p = 1) : d18 p ≤ (0 : Int) + d3560 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5848, d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19862 p hg
    simpa only [d5848, d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d5848, d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19874 p hg
    simpa only [d5848, d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19876 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d3559 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19877 (p : Pattern) (guard : d5849 p = 1) : d2196 p ≤ (0 : Int) + d3561 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5848 p = 1 := by simpa only [d5849, d2196, d3561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19875 p hg
    simpa only [d5849, d2196, d3561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5849, d2196, d3561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19876 p hg
    simpa only [d5849, d2196, d3561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19878 (p : Pattern) (guard : d5849 p = 1) : d2197 p ≤ (0 : Int) + d3562 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2197, d3562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19877 p hg
    simpa only [d2197, d3562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2197, d3562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19846 p hg
    simpa only [d2197, d3562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19879 (p : Pattern) (guard : d5849 p = 1) : d2198 p ≤ (0 : Int) + d3563 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5849 p = 1 := by simpa only [d2198, d3563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19872 p hg
    simpa only [d2198, d3563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5849 p = 1 := by simpa only [d2198, d3563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19878 p hg
    simpa only [d2198, d3563, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
