/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2800 (p : Pattern) (guard : d917 p = 1) : d2 p ≤ (0 : Int) + d259 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d917, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2799 p hg
    simpa only [d917, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2801 (p : Pattern) (guard : d917 p = 1) : d55 p ≤ (0 : Int) + d590 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d55, d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2800 p hg
    simpa only [d55, d590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d55, d590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2796 p hg
    simpa only [d55, d590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2802 (p : Pattern) (guard : d917 p = 1) : d56 p ≤ (0 : Int) + d591 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d56, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2791 p hg
    simpa only [d56, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d56, d591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2801 p hg
    simpa only [d56, d591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2803 (p : Pattern) (guard : d917 p = 1) : d56 p ≤ (0 : Int) + d592 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2798 p hg
    simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2802 p hg
    simpa only [d592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2804 (p : Pattern) (guard : d917 p = 1) : d57 p ≤ (0 : Int) + d593 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d57, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2792 p hg
    simpa only [d57, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d57, d593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2803 p hg
    simpa only [d57, d593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2805 (p : Pattern) (guard : d0 p = 1) : d8 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2806 (p : Pattern) (guard : d917 p = 1) : d8 p ≤ (0 : Int) + d32 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare908 p hg
    simpa only [d917, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2805 p hg
    simpa only [d917, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2807 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2808 (p : Pattern) (guard : d917 p = 1) : d10 p ≤ (0 : Int) + d32 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d10, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare908 p hg
    simpa only [d917, d10, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d10, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2807 p hg
    simpa only [d917, d10, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2809 (p : Pattern) (guard : d917 p = 1) : d11 p ≤ (0 : Int) + d32 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2806 p hg
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2808 p hg
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2810 (p : Pattern) (guard : d917 p = 1) : d12 p ≤ (0 : Int) + d33 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d12, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2791 p hg
    simpa only [d12, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d12, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2809 p hg
    simpa only [d12, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2811 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2812 (p : Pattern) (guard : d917 p = 1) : d9 p ≤ (0 : Int) + d594 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare913 p hg
    simpa only [d917, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2811 p hg
    simpa only [d917, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2813 (p : Pattern) (guard : d0 p = 1) : d58 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2814 (p : Pattern) (guard : d917 p = 1) : d59 p ≤ (0 : Int) + d594 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d59, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare913 p hg
    simpa only [d917, d59, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d59, d594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2813 p hg
    simpa only [d917, d59, d594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2815 (p : Pattern) (guard : d917 p = 1) : d60 p ≤ (0 : Int) + d594 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2812 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2814 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2816 (p : Pattern) (guard : d917 p = 1) : d61 p ≤ (0 : Int) + d595 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d61, d595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2809 p hg
    simpa only [d61, d595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d61, d595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2815 p hg
    simpa only [d61, d595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2817 (p : Pattern) (guard : d917 p = 1) : d62 p ≤ (0 : Int) + d596 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d62, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2802 p hg
    simpa only [d62, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d62, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2816 p hg
    simpa only [d62, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2818 (p : Pattern) (guard : d917 p = 1) : d63 p ≤ (0 : Int) + d597 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d63, d597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2810 p hg
    simpa only [d63, d597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d63, d597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2817 p hg
    simpa only [d63, d597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2819 (p : Pattern) (guard : d917 p = 1) : d64 p ≤ (0 : Int) + d598 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d64, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2804 p hg
    simpa only [d64, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d64, d598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2818 p hg
    simpa only [d64, d598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2820 (p : Pattern) (guard : d917 p = 1) : d55 p ≤ (0 : Int) + d599 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2797 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2801 p hg
    simpa only [d599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2821 (p : Pattern) (guard : d917 p = 1) : d106 p ≤ (0 : Int) + d600 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d106, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2792 p hg
    simpa only [d106, d600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d106, d600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2820 p hg
    simpa only [d106, d600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2822 (p : Pattern) (guard : d917 p = 1) : d119 p ≤ (0 : Int) + d601 p := by
  cases selected : p 187 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d119, d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2788 p hg
    simpa only [d119, d601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d119, d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2797 p hg
    simpa only [d119, d601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2823 (p : Pattern) (guard : d917 p = 1) : d120 p ≤ (0 : Int) + d602 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d120, d602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2788 p hg
    simpa only [d120, d602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d120, d602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2822 p hg
    simpa only [d120, d602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2824 (p : Pattern) (guard : d917 p = 1) : d119 p ≤ (0 : Int) + d603 p := by
  cases selected : p 187 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d119, d603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2791 p hg
    simpa only [d119, d603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d119, d603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2801 p hg
    simpa only [d119, d603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2825 (p : Pattern) (guard : d917 p = 1) : d120 p ≤ (0 : Int) + d604 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d120, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2791 p hg
    simpa only [d120, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d120, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2824 p hg
    simpa only [d120, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2826 (p : Pattern) (guard : d917 p = 1) : d120 p ≤ (0 : Int) + d605 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2823 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2825 p hg
    simpa only [d605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2827 (p : Pattern) (guard : d917 p = 1) : d121 p ≤ (0 : Int) + d606 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d121, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2826 p hg
    simpa only [d121, d606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d121, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2820 p hg
    simpa only [d121, d606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2828 (p : Pattern) (guard : d917 p = 1) : d122 p ≤ (0 : Int) + d607 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d122, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2821 p hg
    simpa only [d122, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d122, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2827 p hg
    simpa only [d122, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2829 (p : Pattern) (guard : d917 p = 1) : d179 p ≤ (0 : Int) + d608 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d179, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2821 p hg
    simpa only [d179, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d179, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2828 p hg
    simpa only [d179, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2830 (p : Pattern) (guard : d917 p = 1) : d65 p ≤ (0 : Int) + d609 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d65, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2801 p hg
    simpa only [d65, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d65, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2815 p hg
    simpa only [d65, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2831 (p : Pattern) (guard : d917 p = 1) : d109 p ≤ (0 : Int) + d610 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d109, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2810 p hg
    simpa only [d109, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d109, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2830 p hg
    simpa only [d109, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2832 (p : Pattern) (guard : d917 p = 1) : d125 p ≤ (0 : Int) + d611 p := by
  cases selected : p 187 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d125, d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2809 p hg
    simpa only [d125, d611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d125, d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2815 p hg
    simpa only [d125, d611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2833 (p : Pattern) (guard : d917 p = 1) : d126 p ≤ (0 : Int) + d612 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d126, d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2809 p hg
    simpa only [d126, d612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d126, d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2832 p hg
    simpa only [d126, d612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2834 (p : Pattern) (guard : d917 p = 1) : d127 p ≤ (0 : Int) + d613 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d127, d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2825 p hg
    simpa only [d127, d613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d127, d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2833 p hg
    simpa only [d127, d613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2835 (p : Pattern) (guard : d917 p = 1) : d128 p ≤ (0 : Int) + d614 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d128, d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2834 p hg
    simpa only [d128, d614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d128, d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2830 p hg
    simpa only [d128, d614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2836 (p : Pattern) (guard : d917 p = 1) : d129 p ≤ (0 : Int) + d615 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d129, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2831 p hg
    simpa only [d129, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d129, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2835 p hg
    simpa only [d129, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2837 (p : Pattern) (guard : d917 p = 1) : d237 p ≤ (0 : Int) + d616 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d237, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2831 p hg
    simpa only [d237, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d237, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2836 p hg
    simpa only [d237, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2838 (p : Pattern) (guard : d917 p = 1) : d238 p ≤ (0 : Int) + d617 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d238, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2829 p hg
    simpa only [d238, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d238, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2837 p hg
    simpa only [d238, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2839 (p : Pattern) (guard : d917 p = 1) : d239 p ≤ (0 : Int) + d618 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d239, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d239, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d239, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2838 p hg
    simpa only [d239, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2840 (p : Pattern) (guard : d917 p = 1) : d68 p ≤ (0 : Int) + d619 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d68, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2804 p hg
    simpa only [d68, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d68, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2820 p hg
    simpa only [d68, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2841 (p : Pattern) (guard : d917 p = 1) : d69 p ≤ (0 : Int) + d620 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d69, d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2818 p hg
    simpa only [d69, d620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d69, d620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2830 p hg
    simpa only [d69, d620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2842 (p : Pattern) (guard : d917 p = 1) : d70 p ≤ (0 : Int) + d621 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d70, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2840 p hg
    simpa only [d70, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d70, d621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2841 p hg
    simpa only [d70, d621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2843 (p : Pattern) (guard : d917 p = 1) : d181 p ≤ (0 : Int) + d622 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d181, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2828 p hg
    simpa only [d181, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d181, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2820 p hg
    simpa only [d181, d622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2844 (p : Pattern) (guard : d917 p = 1) : d240 p ≤ (0 : Int) + d623 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d240, d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2836 p hg
    simpa only [d240, d623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d240, d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2830 p hg
    simpa only [d240, d623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2845 (p : Pattern) (guard : d917 p = 1) : d241 p ≤ (0 : Int) + d624 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d241, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2843 p hg
    simpa only [d241, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d241, d624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2844 p hg
    simpa only [d241, d624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2846 (p : Pattern) (guard : d917 p = 1) : d242 p ≤ (0 : Int) + d625 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d242, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2842 p hg
    simpa only [d242, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d242, d625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2845 p hg
    simpa only [d242, d625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2847 (p : Pattern) (guard : d917 p = 1) : d243 p ≤ (0 : Int) + d626 p := by
  cases selected : p 133 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d243, d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2839 p hg
    simpa only [d243, d626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d243, d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2846 p hg
    simpa only [d243, d626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2848 (p : Pattern) (guard : d917 p = 1) : d66 p ≤ (0 : Int) + d627 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d66, d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2820 p hg
    simpa only [d66, d627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d66, d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2830 p hg
    simpa only [d66, d627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2849 (p : Pattern) (guard : d917 p = 1) : d244 p ≤ (0 : Int) + d628 p := by
  cases selected : p 133 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d244, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2846 p hg
    simpa only [d244, d628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d244, d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2848 p hg
    simpa only [d244, d628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2850 (p : Pattern) (guard : d917 p = 1) : d245 p ≤ (0 : Int) + d629 p := by
  cases selected : p 132 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d245, d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2847 p hg
    simpa only [d245, d629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d245, d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2849 p hg
    simpa only [d245, d629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2851 (p : Pattern) (guard : d917 p = 1) : d137 p ≤ (0 : Int) + d630 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d137, d630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2822 p hg
    simpa only [d137, d630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d137, d630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2797 p hg
    simpa only [d137, d630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2852 (p : Pattern) (guard : d917 p = 1) : d137 p ≤ (0 : Int) + d631 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d137, d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2824 p hg
    simpa only [d137, d631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d137, d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2801 p hg
    simpa only [d137, d631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2853 (p : Pattern) (guard : d917 p = 1) : d137 p ≤ (0 : Int) + d632 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2851 p hg
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2852 p hg
    simpa only [d632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2854 (p : Pattern) (guard : d917 p = 1) : d139 p ≤ (0 : Int) + d633 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d139, d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2826 p hg
    simpa only [d139, d633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d139, d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2853 p hg
    simpa only [d139, d633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2855 (p : Pattern) (guard : d917 p = 1) : d153 p ≤ (0 : Int) + d634 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d153, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2804 p hg
    simpa only [d153, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d153, d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2854 p hg
    simpa only [d153, d634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2856 (p : Pattern) (guard : d917 p = 1) : d186 p ≤ (0 : Int) + d635 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d186, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2804 p hg
    simpa only [d186, d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d186, d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2855 p hg
    simpa only [d186, d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2857 (p : Pattern) (guard : d917 p = 1) : d143 p ≤ (0 : Int) + d636 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d143, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2832 p hg
    simpa only [d143, d636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d143, d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2815 p hg
    simpa only [d143, d636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2858 (p : Pattern) (guard : d917 p = 1) : d144 p ≤ (0 : Int) + d637 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d144, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2852 p hg
    simpa only [d144, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d144, d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2857 p hg
    simpa only [d144, d637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2859 (p : Pattern) (guard : d917 p = 1) : d146 p ≤ (0 : Int) + d638 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d146, d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2834 p hg
    simpa only [d146, d638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d146, d638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2858 p hg
    simpa only [d146, d638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2860 (p : Pattern) (guard : d917 p = 1) : d155 p ≤ (0 : Int) + d639 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d155, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2818 p hg
    simpa only [d155, d639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d155, d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2859 p hg
    simpa only [d155, d639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2861 (p : Pattern) (guard : d917 p = 1) : d246 p ≤ (0 : Int) + d640 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d246, d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2818 p hg
    simpa only [d246, d640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d246, d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2860 p hg
    simpa only [d246, d640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2862 (p : Pattern) (guard : d917 p = 1) : d247 p ≤ (0 : Int) + d641 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d247, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2856 p hg
    simpa only [d247, d641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d247, d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2861 p hg
    simpa only [d247, d641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2863 (p : Pattern) (guard : d917 p = 1) : d248 p ≤ (0 : Int) + d642 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d248, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2862 p hg
    simpa only [d248, d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d248, d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2848 p hg
    simpa only [d248, d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2864 (p : Pattern) (guard : d917 p = 1) : d138 p ≤ (0 : Int) + d643 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d138, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2792 p hg
    simpa only [d138, d643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d138, d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2853 p hg
    simpa only [d138, d643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2865 (p : Pattern) (guard : d917 p = 1) : d140 p ≤ (0 : Int) + d644 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d140, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2864 p hg
    simpa only [d140, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d140, d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2854 p hg
    simpa only [d140, d644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2866 (p : Pattern) (guard : d917 p = 1) : d188 p ≤ (0 : Int) + d645 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d188, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2865 p hg
    simpa only [d188, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d188, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2820 p hg
    simpa only [d188, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2867 (p : Pattern) (guard : d917 p = 1) : d145 p ≤ (0 : Int) + d646 p := by
  cases selected : p 160 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d145, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2810 p hg
    simpa only [d145, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d145, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2858 p hg
    simpa only [d145, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2868 (p : Pattern) (guard : d917 p = 1) : d147 p ≤ (0 : Int) + d647 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d147, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2867 p hg
    simpa only [d147, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d147, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2859 p hg
    simpa only [d147, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2869 (p : Pattern) (guard : d917 p = 1) : d249 p ≤ (0 : Int) + d648 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d249, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2868 p hg
    simpa only [d249, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d249, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2830 p hg
    simpa only [d249, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2870 (p : Pattern) (guard : d917 p = 1) : d250 p ≤ (0 : Int) + d649 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d250, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2866 p hg
    simpa only [d250, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d250, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2869 p hg
    simpa only [d250, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2871 (p : Pattern) (guard : d917 p = 1) : d251 p ≤ (0 : Int) + d650 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d251, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2870 p hg
    simpa only [d251, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d251, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2848 p hg
    simpa only [d251, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2872 (p : Pattern) (guard : d917 p = 1) : d252 p ≤ (0 : Int) + d651 p := by
  cases selected : p 133 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d252, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2863 p hg
    simpa only [d252, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d252, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2871 p hg
    simpa only [d252, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2873 (p : Pattern) (guard : d917 p = 1) : d191 p ≤ (0 : Int) + d652 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d191, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2855 p hg
    simpa only [d191, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d191, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2820 p hg
    simpa only [d191, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2874 (p : Pattern) (guard : d917 p = 1) : d253 p ≤ (0 : Int) + d653 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d253, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2860 p hg
    simpa only [d253, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d253, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2830 p hg
    simpa only [d253, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2875 (p : Pattern) (guard : d917 p = 1) : d254 p ≤ (0 : Int) + d654 p := by
  cases selected : p 141 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d254, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2873 p hg
    simpa only [d254, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d254, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2874 p hg
    simpa only [d254, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2876 (p : Pattern) (guard : d917 p = 1) : d255 p ≤ (0 : Int) + d655 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d255, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2875 p hg
    simpa only [d255, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d255, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2848 p hg
    simpa only [d255, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2877 (p : Pattern) (guard : d917 p = 1) : d256 p ≤ (0 : Int) + d656 p := by
  cases selected : p 133 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d256, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2876 p hg
    simpa only [d256, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d256, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2848 p hg
    simpa only [d256, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2878 (p : Pattern) (guard : d917 p = 1) : d257 p ≤ (0 : Int) + d657 p := by
  cases selected : p 132 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d257, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2872 p hg
    simpa only [d257, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d257, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2877 p hg
    simpa only [d257, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2879 (p : Pattern) (guard : d917 p = 1) : d258 p ≤ (0 : Int) + d658 p := by
  cases selected : p 108 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d258, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2850 p hg
    simpa only [d258, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d258, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2878 p hg
    simpa only [d258, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2880 (p : Pattern) (guard : d854 p = 1) : d258 p ≤ (0 : Int) + d258 p := by
  omega
theorem compare2881 (p : Pattern) (guard : d916 p = 1) : d0 p ≤ (2 : Int) + d0 p := by
  omega
theorem compare2882 (p : Pattern) (guard : d916 p = 1) : d6 p ≤ (2 : Int) + d0 p := by
  cases selected : p 193 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d916, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2640 p hg
    simpa only [d916, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d916, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d916, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2883 (p : Pattern) (guard : d916 p = 1) : d7 p ≤ (2 : Int) + d0 p := by
  cases selected : p 192 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2881 p hg
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2882 p hg
    simpa only [d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2884 (p : Pattern) (guard : d916 p = 1) : d2 p ≤ (2 : Int) + d2 p := by
  omega
theorem compare2885 (p : Pattern) (guard : d916 p = 1) : d54 p ≤ (2 : Int) + d2 p := by
  cases selected : p 193 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d916, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2644 p hg
    simpa only [d916, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d916, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare75 p hg
    simpa only [d916, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2886 (p : Pattern) (guard : d916 p = 1) : d55 p ≤ (2 : Int) + d2 p := by
  cases selected : p 192 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2884 p hg
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2885 p hg
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2887 (p : Pattern) (guard : d916 p = 1) : d56 p ≤ (2 : Int) + d45 p := by
  cases selected : p 186 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d56, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2883 p hg
    simpa only [d56, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d56, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2886 p hg
    simpa only [d56, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2888 (p : Pattern) (guard : d916 p = 1) : d57 p ≤ (2 : Int) + d46 p := by
  cases selected : p 160 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d57, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2883 p hg
    simpa only [d57, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d57, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2887 p hg
    simpa only [d57, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2889 (p : Pattern) (guard : d916 p = 1) : d8 p ≤ (2 : Int) + d8 p := by
  omega
theorem compare2890 (p : Pattern) (guard : d916 p = 1) : d10 p ≤ (2 : Int) + d8 p := by
  cases selected : p 193 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d916, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2650 p hg
    simpa only [d916, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d916, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare84 p hg
    simpa only [d916, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2891 (p : Pattern) (guard : d916 p = 1) : d11 p ≤ (2 : Int) + d8 p := by
  cases selected : p 192 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2889 p hg
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2890 p hg
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2892 (p : Pattern) (guard : d916 p = 1) : d12 p ≤ (2 : Int) + d1055 p := by
  cases selected : p 168 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d12, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2883 p hg
    simpa only [d12, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d12, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2891 p hg
    simpa only [d12, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2893 (p : Pattern) (guard : d916 p = 1) : d9 p ≤ (2 : Int) + d9 p := by
  omega
theorem compare2894 (p : Pattern) (guard : d916 p = 1) : d59 p ≤ (2 : Int) + d9 p := by
  cases selected : p 193 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d916, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2655 p hg
    simpa only [d916, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d916, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare86 p hg
    simpa only [d916, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2895 (p : Pattern) (guard : d916 p = 1) : d60 p ≤ (2 : Int) + d9 p := by
  cases selected : p 192 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2893 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2894 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2896 (p : Pattern) (guard : d916 p = 1) : d61 p ≤ (2 : Int) + d1056 p := by
  cases selected : p 186 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d61, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2891 p hg
    simpa only [d61, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d61, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2895 p hg
    simpa only [d61, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2897 (p : Pattern) (guard : d916 p = 1) : d62 p ≤ (2 : Int) + d1057 p := by
  cases selected : p 168 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d62, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2887 p hg
    simpa only [d62, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d62, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2896 p hg
    simpa only [d62, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2898 (p : Pattern) (guard : d916 p = 1) : d63 p ≤ (2 : Int) + d1058 p := by
  cases selected : p 160 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d63, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2892 p hg
    simpa only [d63, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d63, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2897 p hg
    simpa only [d63, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2899 (p : Pattern) (guard : d916 p = 1) : d64 p ≤ (2 : Int) + d1059 p := by
  cases selected : p 141 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d64, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2888 p hg
    simpa only [d64, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d64, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2898 p hg
    simpa only [d64, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2900 (p : Pattern) (guard : d916 p = 1) : d106 p ≤ (2 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d106, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2883 p hg
    simpa only [d106, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d106, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2886 p hg
    simpa only [d106, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2901 (p : Pattern) (guard : d916 p = 1) : d119 p ≤ (2 : Int) + d82 p := by
  cases selected : p 187 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d119, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2883 p hg
    simpa only [d119, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d119, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2886 p hg
    simpa only [d119, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2902 (p : Pattern) (guard : d916 p = 1) : d120 p ≤ (2 : Int) + d83 p := by
  cases selected : p 186 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d120, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2883 p hg
    simpa only [d120, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d120, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2901 p hg
    simpa only [d120, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2903 (p : Pattern) (guard : d916 p = 1) : d121 p ≤ (2 : Int) + d84 p := by
  cases selected : p 160 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d121, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2902 p hg
    simpa only [d121, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d121, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2886 p hg
    simpa only [d121, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2904 (p : Pattern) (guard : d916 p = 1) : d122 p ≤ (2 : Int) + d85 p := by
  cases selected : p 159 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d122, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2900 p hg
    simpa only [d122, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d122, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2903 p hg
    simpa only [d122, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2905 (p : Pattern) (guard : d916 p = 1) : d179 p ≤ (2 : Int) + d162 p := by
  cases selected : p 158 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d179, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2900 p hg
    simpa only [d179, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d179, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2904 p hg
    simpa only [d179, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2906 (p : Pattern) (guard : d916 p = 1) : d65 p ≤ (2 : Int) + d1060 p := by
  cases selected : p 168 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d65, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2886 p hg
    simpa only [d65, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d65, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2895 p hg
    simpa only [d65, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2907 (p : Pattern) (guard : d916 p = 1) : d109 p ≤ (2 : Int) + d1061 p := by
  cases selected : p 160 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d109, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2892 p hg
    simpa only [d109, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d109, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2906 p hg
    simpa only [d109, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2908 (p : Pattern) (guard : d916 p = 1) : d125 p ≤ (2 : Int) + d1062 p := by
  cases selected : p 187 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d125, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2891 p hg
    simpa only [d125, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d125, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2895 p hg
    simpa only [d125, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2909 (p : Pattern) (guard : d916 p = 1) : d126 p ≤ (2 : Int) + d1063 p := by
  cases selected : p 186 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d126, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2891 p hg
    simpa only [d126, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d126, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2908 p hg
    simpa only [d126, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2910 (p : Pattern) (guard : d916 p = 1) : d127 p ≤ (2 : Int) + d1064 p := by
  cases selected : p 168 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d127, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2902 p hg
    simpa only [d127, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d127, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2909 p hg
    simpa only [d127, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2911 (p : Pattern) (guard : d916 p = 1) : d128 p ≤ (2 : Int) + d1065 p := by
  cases selected : p 160 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d128, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2910 p hg
    simpa only [d128, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d128, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2906 p hg
    simpa only [d128, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2912 (p : Pattern) (guard : d916 p = 1) : d129 p ≤ (2 : Int) + d1066 p := by
  cases selected : p 159 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2907 p hg
    simpa only [d129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2911 p hg
    simpa only [d129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2913 (p : Pattern) (guard : d916 p = 1) : d237 p ≤ (2 : Int) + d1067 p := by
  cases selected : p 158 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d237, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2907 p hg
    simpa only [d237, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d237, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2912 p hg
    simpa only [d237, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2914 (p : Pattern) (guard : d916 p = 1) : d238 p ≤ (2 : Int) + d1068 p := by
  cases selected : p 141 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d238, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2905 p hg
    simpa only [d238, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d238, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2913 p hg
    simpa only [d238, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2915 (p : Pattern) (guard : d916 p = 1) : d239 p ≤ (2 : Int) + d1069 p := by
  cases selected : p 134 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d239, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2899 p hg
    simpa only [d239, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d239, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2914 p hg
    simpa only [d239, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2916 (p : Pattern) (guard : d916 p = 1) : d68 p ≤ (2 : Int) + d48 p := by
  cases selected : p 158 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d68, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2888 p hg
    simpa only [d68, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d68, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2886 p hg
    simpa only [d68, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2917 (p : Pattern) (guard : d916 p = 1) : d69 p ≤ (2 : Int) + d1070 p := by
  cases selected : p 158 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d69, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2898 p hg
    simpa only [d69, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d69, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2906 p hg
    simpa only [d69, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2918 (p : Pattern) (guard : d916 p = 1) : d70 p ≤ (2 : Int) + d1071 p := by
  cases selected : p 141 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d70, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2916 p hg
    simpa only [d70, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d70, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2917 p hg
    simpa only [d70, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2919 (p : Pattern) (guard : d916 p = 1) : d181 p ≤ (2 : Int) + d164 p := by
  cases selected : p 158 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d181, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2904 p hg
    simpa only [d181, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d181, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2886 p hg
    simpa only [d181, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2920 (p : Pattern) (guard : d916 p = 1) : d240 p ≤ (2 : Int) + d1072 p := by
  cases selected : p 158 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d240, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2912 p hg
    simpa only [d240, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d240, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2906 p hg
    simpa only [d240, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2921 (p : Pattern) (guard : d916 p = 1) : d241 p ≤ (2 : Int) + d1073 p := by
  cases selected : p 141 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d241, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2919 p hg
    simpa only [d241, d1073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d241, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2920 p hg
    simpa only [d241, d1073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2922 (p : Pattern) (guard : d916 p = 1) : d242 p ≤ (2 : Int) + d1074 p := by
  cases selected : p 134 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d242, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2918 p hg
    simpa only [d242, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d242, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2921 p hg
    simpa only [d242, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2923 (p : Pattern) (guard : d916 p = 1) : d243 p ≤ (2 : Int) + d1075 p := by
  cases selected : p 133 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d243, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2915 p hg
    simpa only [d243, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d243, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2922 p hg
    simpa only [d243, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2924 (p : Pattern) (guard : d916 p = 1) : d66 p ≤ (2 : Int) + d1076 p := by
  cases selected : p 141 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d66, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2886 p hg
    simpa only [d66, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d66, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2906 p hg
    simpa only [d66, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2925 (p : Pattern) (guard : d916 p = 1) : d244 p ≤ (2 : Int) + d1077 p := by
  cases selected : p 133 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d244, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2922 p hg
    simpa only [d244, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d244, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2924 p hg
    simpa only [d244, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2926 (p : Pattern) (guard : d916 p = 1) : d245 p ≤ (2 : Int) + d1078 p := by
  cases selected : p 132 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d245, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2923 p hg
    simpa only [d245, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d245, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2925 p hg
    simpa only [d245, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2927 (p : Pattern) (guard : d916 p = 1) : d137 p ≤ (2 : Int) + d92 p := by
  cases selected : p 186 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d137, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2901 p hg
    simpa only [d137, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d137, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2886 p hg
    simpa only [d137, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2928 (p : Pattern) (guard : d916 p = 1) : d139 p ≤ (2 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d139, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2902 p hg
    simpa only [d139, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d139, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d139, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2929 (p : Pattern) (guard : d916 p = 1) : d153 p ≤ (2 : Int) + d100 p := by
  cases selected : p 159 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d153, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2888 p hg
    simpa only [d153, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d153, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2928 p hg
    simpa only [d153, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2930 (p : Pattern) (guard : d916 p = 1) : d186 p ≤ (2 : Int) + d169 p := by
  cases selected : p 158 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d186, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2888 p hg
    simpa only [d186, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d186, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2929 p hg
    simpa only [d186, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2931 (p : Pattern) (guard : d916 p = 1) : d143 p ≤ (2 : Int) + d1079 p := by
  cases selected : p 186 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d143, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2908 p hg
    simpa only [d143, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d143, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2895 p hg
    simpa only [d143, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2932 (p : Pattern) (guard : d916 p = 1) : d144 p ≤ (2 : Int) + d1080 p := by
  cases selected : p 168 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d144, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d144, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d144, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2931 p hg
    simpa only [d144, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2933 (p : Pattern) (guard : d916 p = 1) : d146 p ≤ (2 : Int) + d1081 p := by
  cases selected : p 160 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d146, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2910 p hg
    simpa only [d146, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d146, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2932 p hg
    simpa only [d146, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2934 (p : Pattern) (guard : d916 p = 1) : d155 p ≤ (2 : Int) + d1082 p := by
  cases selected : p 159 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d155, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2898 p hg
    simpa only [d155, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d155, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2933 p hg
    simpa only [d155, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2935 (p : Pattern) (guard : d916 p = 1) : d246 p ≤ (2 : Int) + d1083 p := by
  cases selected : p 158 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d246, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2898 p hg
    simpa only [d246, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d246, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2934 p hg
    simpa only [d246, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2936 (p : Pattern) (guard : d916 p = 1) : d247 p ≤ (2 : Int) + d1084 p := by
  cases selected : p 141 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d247, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2930 p hg
    simpa only [d247, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d247, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2935 p hg
    simpa only [d247, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2937 (p : Pattern) (guard : d916 p = 1) : d248 p ≤ (2 : Int) + d1085 p := by
  cases selected : p 134 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d248, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2936 p hg
    simpa only [d248, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d248, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2924 p hg
    simpa only [d248, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2938 (p : Pattern) (guard : d916 p = 1) : d138 p ≤ (2 : Int) + d93 p := by
  cases selected : p 160 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d138, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2883 p hg
    simpa only [d138, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d138, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d138, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2939 (p : Pattern) (guard : d916 p = 1) : d140 p ≤ (2 : Int) + d95 p := by
  cases selected : p 159 with
  | false =>
    have hg : d916 p = 1 := by simpa only [d140, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2938 p hg
    simpa only [d140, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d916 p = 1 := by simpa only [d140, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2928 p hg
    simpa only [d140, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
