/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons106
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare14980 (p : Pattern) (guard : d5503 p = 1) : d90 p ≤ (0 : Int) + d2631 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d90, d2631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14979 p hg
    simpa only [d90, d2631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d90, d2631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14932 p hg
    simpa only [d90, d2631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14981 (p : Pattern) (guard : d5503 p = 1) : d91 p ≤ (0 : Int) + d2632 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d91, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14932 p hg
    simpa only [d91, d2632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d91, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d91, d2632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14982 (p : Pattern) (guard : d5503 p = 1) : d92 p ≤ (0 : Int) + d2633 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d92, d2633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14980 p hg
    simpa only [d92, d2633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d92, d2633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14981 p hg
    simpa only [d92, d2633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14983 (p : Pattern) (guard : d5503 p = 1) : d93 p ≤ (0 : Int) + d2634 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d93, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14981 p hg
    simpa only [d93, d2634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d93, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d93, d2634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14984 (p : Pattern) (guard : d5503 p = 1) : d94 p ≤ (0 : Int) + d2635 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d94, d2635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14982 p hg
    simpa only [d94, d2635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d94, d2635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14983 p hg
    simpa only [d94, d2635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14985 (p : Pattern) (guard : d5503 p = 1) : d95 p ≤ (0 : Int) + d2636 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d95, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14983 p hg
    simpa only [d95, d2636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d95, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d95, d2636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14986 (p : Pattern) (guard : d5503 p = 1) : d96 p ≤ (0 : Int) + d2637 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d96, d2637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14984 p hg
    simpa only [d96, d2637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d96, d2637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14985 p hg
    simpa only [d96, d2637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14987 (p : Pattern) (guard : d5503 p = 1) : d97 p ≤ (0 : Int) + d2638 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d97, d2638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14977 p hg
    simpa only [d97, d2638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d97, d2638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14986 p hg
    simpa only [d97, d2638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14988 (p : Pattern) (guard : d5503 p = 1) : d98 p ≤ (0 : Int) + d2639 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d98, d2639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14978 p hg
    simpa only [d98, d2639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d98, d2639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14987 p hg
    simpa only [d98, d2639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14989 (p : Pattern) (guard : d5503 p = 1) : d16 p ≤ (0 : Int) + d2640 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14848 p hg
    simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14852 p hg
    simpa only [d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14990 (p : Pattern) (guard : d5503 p = 1) : d22 p ≤ (0 : Int) + d2641 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d22, d2641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14989 p hg
    simpa only [d22, d2641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d22, d2641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14863 p hg
    simpa only [d22, d2641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14991 (p : Pattern) (guard : d5503 p = 1) : d29 p ≤ (0 : Int) + d2642 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d29, d2642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14990 p hg
    simpa only [d29, d2642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d29, d2642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14876 p hg
    simpa only [d29, d2642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14992 (p : Pattern) (guard : d5503 p = 1) : d52 p ≤ (0 : Int) + d2643 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d52, d2643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14991 p hg
    simpa only [d52, d2643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d52, d2643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14902 p hg
    simpa only [d52, d2643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14993 (p : Pattern) (guard : d5503 p = 1) : d54 p ≤ (0 : Int) + d2644 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d54, d2644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14852 p hg
    simpa only [d54, d2644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d54, d2644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14915 p hg
    simpa only [d54, d2644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14994 (p : Pattern) (guard : d5503 p = 1) : d56 p ≤ (0 : Int) + d2645 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d56, d2645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14993 p hg
    simpa only [d56, d2645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d56, d2645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14917 p hg
    simpa only [d56, d2645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14995 (p : Pattern) (guard : d5503 p = 1) : d65 p ≤ (0 : Int) + d2646 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d65, d2646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14994 p hg
    simpa only [d65, d2646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d65, d2646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14933 p hg
    simpa only [d65, d2646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14996 (p : Pattern) (guard : d5503 p = 1) : d76 p ≤ (0 : Int) + d2647 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d76, d2647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14995 p hg
    simpa only [d76, d2647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d76, d2647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14944 p hg
    simpa only [d76, d2647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14997 (p : Pattern) (guard : d5503 p = 1) : d77 p ≤ (0 : Int) + d2648 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d77, d2648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14992 p hg
    simpa only [d77, d2648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d77, d2648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14996 p hg
    simpa only [d77, d2648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14998 (p : Pattern) (guard : d5503 p = 1) : d88 p ≤ (0 : Int) + d2649 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d88, d2649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14997 p hg
    simpa only [d88, d2649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d88, d2649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14977 p hg
    simpa only [d88, d2649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14999 (p : Pattern) (guard : d5503 p = 1) : d99 p ≤ (0 : Int) + d2650 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d99, d2650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14977 p hg
    simpa only [d99, d2650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d99, d2650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d99, d2650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15000 (p : Pattern) (guard : d5503 p = 1) : d100 p ≤ (0 : Int) + d2651 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d100, d2651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14998 p hg
    simpa only [d100, d2651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d100, d2651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14999 p hg
    simpa only [d100, d2651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15001 (p : Pattern) (guard : d5503 p = 1) : d101 p ≤ (0 : Int) + d2652 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d101, d2652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14988 p hg
    simpa only [d101, d2652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d101, d2652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15000 p hg
    simpa only [d101, d2652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15002 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d356 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15003 (p : Pattern) (guard : d5502 p = 1) : d14 p ≤ (0 : Int) + d2653 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d5502, d2653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15002 p hg
    simpa only [d5502, d2653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15004 (p : Pattern) (guard : d5503 p = 1) : d14 p ≤ (0 : Int) + d2654 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15003 p hg
    simpa only [d5503, d2654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14833 p hg
    simpa only [d5503, d2654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15005 (p : Pattern) (guard : d5503 p = 1) : d14 p ≤ (0 : Int) + d2655 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15004 p hg
    simpa only [d2655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14837 p hg
    simpa only [d2655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15006 (p : Pattern) (guard : d5503 p = 1) : d16 p ≤ (0 : Int) + d2656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d16, d2656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15005 p hg
    simpa only [d16, d2656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d16, d2656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14842 p hg
    simpa only [d16, d2656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15007 (p : Pattern) (guard : d5503 p = 1) : d16 p ≤ (0 : Int) + d2657 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15006 p hg
    simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14852 p hg
    simpa only [d2657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15008 (p : Pattern) (guard : d5503 p = 1) : d22 p ≤ (0 : Int) + d2658 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d22, d2658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15007 p hg
    simpa only [d22, d2658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d22, d2658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14863 p hg
    simpa only [d22, d2658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15009 (p : Pattern) (guard : d5503 p = 1) : d29 p ≤ (0 : Int) + d2659 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d29, d2659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15008 p hg
    simpa only [d29, d2659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d29, d2659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14876 p hg
    simpa only [d29, d2659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15010 (p : Pattern) (guard : d5503 p = 1) : d52 p ≤ (0 : Int) + d2660 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d52, d2660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15009 p hg
    simpa only [d52, d2660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d52, d2660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14902 p hg
    simpa only [d52, d2660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15011 (p : Pattern) (guard : d5503 p = 1) : d54 p ≤ (0 : Int) + d2661 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d54, d2661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14848 p hg
    simpa only [d54, d2661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d54, d2661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14915 p hg
    simpa only [d54, d2661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15012 (p : Pattern) (guard : d5503 p = 1) : d56 p ≤ (0 : Int) + d2662 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d56, d2662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15011 p hg
    simpa only [d56, d2662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d56, d2662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14917 p hg
    simpa only [d56, d2662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15013 (p : Pattern) (guard : d5503 p = 1) : d65 p ≤ (0 : Int) + d2663 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d65, d2663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15012 p hg
    simpa only [d65, d2663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d65, d2663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14933 p hg
    simpa only [d65, d2663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15014 (p : Pattern) (guard : d5503 p = 1) : d76 p ≤ (0 : Int) + d2664 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d76, d2664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15013 p hg
    simpa only [d76, d2664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d76, d2664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14944 p hg
    simpa only [d76, d2664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15015 (p : Pattern) (guard : d5503 p = 1) : d77 p ≤ (0 : Int) + d2665 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d77, d2665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15010 p hg
    simpa only [d77, d2665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d77, d2665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15014 p hg
    simpa only [d77, d2665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15016 (p : Pattern) (guard : d5503 p = 1) : d88 p ≤ (0 : Int) + d2666 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d88, d2666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15015 p hg
    simpa only [d88, d2666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d88, d2666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14977 p hg
    simpa only [d88, d2666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15017 (p : Pattern) (guard : d5503 p = 1) : d98 p ≤ (0 : Int) + d2667 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d98, d2667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15016 p hg
    simpa only [d98, d2667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d98, d2667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14987 p hg
    simpa only [d98, d2667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15018 (p : Pattern) (guard : d5503 p = 1) : d22 p ≤ (0 : Int) + d2668 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d22, d2668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14852 p hg
    simpa only [d22, d2668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d22, d2668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14863 p hg
    simpa only [d22, d2668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15019 (p : Pattern) (guard : d5503 p = 1) : d29 p ≤ (0 : Int) + d2669 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d29, d2669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15018 p hg
    simpa only [d29, d2669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d29, d2669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14876 p hg
    simpa only [d29, d2669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15020 (p : Pattern) (guard : d5503 p = 1) : d52 p ≤ (0 : Int) + d2670 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d52, d2670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15019 p hg
    simpa only [d52, d2670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d52, d2670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14902 p hg
    simpa only [d52, d2670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15021 (p : Pattern) (guard : d5503 p = 1) : d77 p ≤ (0 : Int) + d2671 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d77, d2671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15020 p hg
    simpa only [d77, d2671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d77, d2671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14996 p hg
    simpa only [d77, d2671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15022 (p : Pattern) (guard : d5503 p = 1) : d88 p ≤ (0 : Int) + d2672 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d88, d2672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15021 p hg
    simpa only [d88, d2672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d88, d2672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14977 p hg
    simpa only [d88, d2672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15023 (p : Pattern) (guard : d5503 p = 1) : d100 p ≤ (0 : Int) + d2673 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d100, d2673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15022 p hg
    simpa only [d100, d2673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d100, d2673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14999 p hg
    simpa only [d100, d2673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15024 (p : Pattern) (guard : d5503 p = 1) : d101 p ≤ (0 : Int) + d2674 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d101, d2674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15017 p hg
    simpa only [d101, d2674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d101, d2674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15023 p hg
    simpa only [d101, d2674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15025 (p : Pattern) (guard : d5503 p = 1) : d101 p ≤ (0 : Int) + d2675 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15001 p hg
    simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15024 p hg
    simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15026 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (0 : Int) + d356 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15027 (p : Pattern) (guard : d5502 p = 1) : d103 p ≤ (0 : Int) + d2676 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d5502, d2676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15026 p hg
    simpa only [d5502, d2676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15028 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (0 : Int) + d2677 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15029 (p : Pattern) (guard : d5503 p = 1) : d103 p ≤ (0 : Int) + d2678 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15027 p hg
    simpa only [d5503, d2678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15028 p hg
    simpa only [d5503, d2678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15030 (p : Pattern) (guard : d5502 p = 1) : d103 p ≤ (0 : Int) + d2677 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d5502, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d5502, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15031 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (0 : Int) + d2679 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15032 (p : Pattern) (guard : d5503 p = 1) : d103 p ≤ (0 : Int) + d2680 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15030 p hg
    simpa only [d5503, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15031 p hg
    simpa only [d5503, d2680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15033 (p : Pattern) (guard : d5503 p = 1) : d103 p ≤ (0 : Int) + d2681 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15029 p hg
    simpa only [d2681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15032 p hg
    simpa only [d2681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15034 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (0 : Int) + d2682 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15035 (p : Pattern) (guard : d5503 p = 1) : d103 p ≤ (0 : Int) + d2683 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15030 p hg
    simpa only [d5503, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15034 p hg
    simpa only [d5503, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15036 (p : Pattern) (guard : d5503 p = 1) : d104 p ≤ (0 : Int) + d2684 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d104, d2684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15035 p hg
    simpa only [d104, d2684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d104, d2684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d104, d2684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15037 (p : Pattern) (guard : d5503 p = 1) : d105 p ≤ (0 : Int) + d2685 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d105, d2685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15033 p hg
    simpa only [d105, d2685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d105, d2685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15036 p hg
    simpa only [d105, d2685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15038 (p : Pattern) (guard : d5503 p = 1) : d103 p ≤ (0 : Int) + d2677 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15030 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15028 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15039 (p : Pattern) (guard : d5503 p = 1) : d103 p ≤ (0 : Int) + d2686 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15038 p hg
    simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15032 p hg
    simpa only [d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15040 (p : Pattern) (guard : d5503 p = 1) : d105 p ≤ (0 : Int) + d2687 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d105, d2687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15039 p hg
    simpa only [d105, d2687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d105, d2687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15036 p hg
    simpa only [d105, d2687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15041 (p : Pattern) (guard : d5503 p = 1) : d105 p ≤ (0 : Int) + d2688 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15037 p hg
    simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15040 p hg
    simpa only [d2688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15042 (p : Pattern) (guard : d5502 p = 1) : d107 p ≤ (0 : Int) + d2689 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d5502, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d5502, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15043 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (0 : Int) + d2689 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15044 (p : Pattern) (guard : d5503 p = 1) : d107 p ≤ (0 : Int) + d2689 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15042 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15043 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15045 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (0 : Int) + d2690 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15046 (p : Pattern) (guard : d5503 p = 1) : d107 p ≤ (0 : Int) + d2691 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15042 p hg
    simpa only [d5503, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15045 p hg
    simpa only [d5503, d2691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15047 (p : Pattern) (guard : d5503 p = 1) : d107 p ≤ (0 : Int) + d2692 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15044 p hg
    simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15046 p hg
    simpa only [d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15048 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (0 : Int) + d2693 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15049 (p : Pattern) (guard : d5503 p = 1) : d107 p ≤ (0 : Int) + d2694 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15042 p hg
    simpa only [d5503, d2694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15048 p hg
    simpa only [d5503, d2694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15050 (p : Pattern) (guard : d5503 p = 1) : d108 p ≤ (0 : Int) + d2695 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d108, d2695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15049 p hg
    simpa only [d108, d2695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d108, d2695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d108, d2695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15051 (p : Pattern) (guard : d5503 p = 1) : d109 p ≤ (0 : Int) + d2696 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d109, d2696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15047 p hg
    simpa only [d109, d2696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d109, d2696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15050 p hg
    simpa only [d109, d2696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15052 (p : Pattern) (guard : d5503 p = 1) : d110 p ≤ (0 : Int) + d2697 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d110, d2697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15040 p hg
    simpa only [d110, d2697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d110, d2697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15051 p hg
    simpa only [d110, d2697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15053 (p : Pattern) (guard : d5503 p = 1) : d111 p ≤ (0 : Int) + d2698 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d111, d2698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15041 p hg
    simpa only [d111, d2698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d111, d2698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15052 p hg
    simpa only [d111, d2698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15054 (p : Pattern) (guard : d5503 p = 1) : d112 p ≤ (0 : Int) + d2699 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d112, d2699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14926 p hg
    simpa only [d112, d2699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d112, d2699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d112, d2699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15055 (p : Pattern) (guard : d5503 p = 1) : d113 p ≤ (0 : Int) + d2700 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d113, d2700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15052 p hg
    simpa only [d113, d2700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d113, d2700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15054 p hg
    simpa only [d113, d2700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15056 (p : Pattern) (guard : d5503 p = 1) : d114 p ≤ (0 : Int) + d2701 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d114, d2701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15053 p hg
    simpa only [d114, d2701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d114, d2701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15055 p hg
    simpa only [d114, d2701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15057 (p : Pattern) (guard : d5502 p = 1) : d116 p ≤ (0 : Int) + d2702 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d5502, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11639 p hg
    simpa only [d5502, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15058 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (0 : Int) + d2703 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15059 (p : Pattern) (guard : d5503 p = 1) : d116 p ≤ (0 : Int) + d2704 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15057 p hg
    simpa only [d5503, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15058 p hg
    simpa only [d5503, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15060 (p : Pattern) (guard : d5503 p = 1) : d117 p ≤ (0 : Int) + d2705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d117, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15059 p hg
    simpa only [d117, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d117, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d117, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15061 (p : Pattern) (guard : d5503 p = 1) : d118 p ≤ (0 : Int) + d2706 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d118, d2706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15039 p hg
    simpa only [d118, d2706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d118, d2706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15060 p hg
    simpa only [d118, d2706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15062 (p : Pattern) (guard : d5502 p = 1) : d120 p ≤ (0 : Int) + d2707 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3159 p hg
    simpa only [d5502, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11672 p hg
    simpa only [d5502, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15063 (p : Pattern) (guard : d0 p = 1) : d120 p ≤ (0 : Int) + d2708 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15064 (p : Pattern) (guard : d5503 p = 1) : d120 p ≤ (0 : Int) + d2709 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15062 p hg
    simpa only [d5503, d2709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15063 p hg
    simpa only [d5503, d2709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15065 (p : Pattern) (guard : d5503 p = 1) : d121 p ≤ (0 : Int) + d2710 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d121, d2710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15064 p hg
    simpa only [d121, d2710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d121, d2710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d121, d2710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15066 (p : Pattern) (guard : d5503 p = 1) : d122 p ≤ (0 : Int) + d2711 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d122, d2711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15039 p hg
    simpa only [d122, d2711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d122, d2711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15065 p hg
    simpa only [d122, d2711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15067 (p : Pattern) (guard : d5503 p = 1) : d123 p ≤ (0 : Int) + d2712 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d123, d2712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15061 p hg
    simpa only [d123, d2712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d123, d2712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15066 p hg
    simpa only [d123, d2712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15068 (p : Pattern) (guard : d5503 p = 1) : d124 p ≤ (0 : Int) + d2713 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d124, d2713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15039 p hg
    simpa only [d124, d2713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d124, d2713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d124, d2713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15069 (p : Pattern) (guard : d5503 p = 1) : d125 p ≤ (0 : Int) + d2714 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d125, d2714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15047 p hg
    simpa only [d125, d2714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d125, d2714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d125, d2714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15070 (p : Pattern) (guard : d5503 p = 1) : d126 p ≤ (0 : Int) + d2715 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d126, d2715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15068 p hg
    simpa only [d126, d2715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d126, d2715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15069 p hg
    simpa only [d126, d2715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15071 (p : Pattern) (guard : d5503 p = 1) : d127 p ≤ (0 : Int) + d2716 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d127, d2716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15067 p hg
    simpa only [d127, d2716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d127, d2716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15070 p hg
    simpa only [d127, d2716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15072 (p : Pattern) (guard : d5503 p = 1) : d128 p ≤ (0 : Int) + d2717 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d128, d2717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14939 p hg
    simpa only [d128, d2717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d128, d2717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d128, d2717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15073 (p : Pattern) (guard : d5503 p = 1) : d129 p ≤ (0 : Int) + d2718 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d129, d2718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15070 p hg
    simpa only [d129, d2718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d129, d2718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15072 p hg
    simpa only [d129, d2718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15074 (p : Pattern) (guard : d5503 p = 1) : d130 p ≤ (0 : Int) + d2719 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d130, d2719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15071 p hg
    simpa only [d130, d2719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d130, d2719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15073 p hg
    simpa only [d130, d2719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15075 (p : Pattern) (guard : d5503 p = 1) : d131 p ≤ (0 : Int) + d2720 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d131, d2720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15056 p hg
    simpa only [d131, d2720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d131, d2720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15074 p hg
    simpa only [d131, d2720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15076 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (0 : Int) + d327 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15077 (p : Pattern) (guard : d5502 p = 1) : d103 p ≤ (0 : Int) + d2721 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d5502, d2721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15076 p hg
    simpa only [d5502, d2721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15078 (p : Pattern) (guard : d5503 p = 1) : d103 p ≤ (0 : Int) + d2722 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15077 p hg
    simpa only [d5503, d2722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15028 p hg
    simpa only [d5503, d2722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15079 (p : Pattern) (guard : d5503 p = 1) : d103 p ≤ (0 : Int) + d2723 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15078 p hg
    simpa only [d2723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15032 p hg
    simpa only [d2723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15080 (p : Pattern) (guard : d5503 p = 1) : d105 p ≤ (0 : Int) + d2724 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d105, d2724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15079 p hg
    simpa only [d105, d2724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d105, d2724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15036 p hg
    simpa only [d105, d2724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15081 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (0 : Int) + d2702 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15082 (p : Pattern) (guard : d5503 p = 1) : d116 p ≤ (0 : Int) + d2702 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15057 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15081 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15083 (p : Pattern) (guard : d5503 p = 1) : d116 p ≤ (0 : Int) + d2725 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15082 p hg
    simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15059 p hg
    simpa only [d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15084 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (0 : Int) + d2726 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15085 (p : Pattern) (guard : d5503 p = 1) : d116 p ≤ (0 : Int) + d2727 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15057 p hg
    simpa only [d5503, d2727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15084 p hg
    simpa only [d5503, d2727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15086 (p : Pattern) (guard : d5503 p = 1) : d117 p ≤ (0 : Int) + d2728 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d117, d2728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15085 p hg
    simpa only [d117, d2728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d117, d2728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d117, d2728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15087 (p : Pattern) (guard : d5503 p = 1) : d132 p ≤ (0 : Int) + d2729 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d132, d2729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15083 p hg
    simpa only [d132, d2729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d132, d2729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15086 p hg
    simpa only [d132, d2729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15088 (p : Pattern) (guard : d5503 p = 1) : d133 p ≤ (0 : Int) + d2730 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d133, d2730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15080 p hg
    simpa only [d133, d2730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d133, d2730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15087 p hg
    simpa only [d133, d2730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15089 (p : Pattern) (guard : d5503 p = 1) : d134 p ≤ (0 : Int) + d2731 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d134, d2731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15051 p hg
    simpa only [d134, d2731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d134, d2731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14926 p hg
    simpa only [d134, d2731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15090 (p : Pattern) (guard : d5503 p = 1) : d135 p ≤ (0 : Int) + d2732 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d135, d2732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15088 p hg
    simpa only [d135, d2732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d135, d2732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15089 p hg
    simpa only [d135, d2732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15091 (p : Pattern) (guard : d5503 p = 1) : d136 p ≤ (0 : Int) + d2733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d136, d2733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15051 p hg
    simpa only [d136, d2733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d136, d2733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14931 p hg
    simpa only [d136, d2733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15092 (p : Pattern) (guard : d5503 p = 1) : d137 p ≤ (0 : Int) + d2734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d137, d2734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15091 p hg
    simpa only [d137, d2734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d137, d2734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d137, d2734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15093 (p : Pattern) (guard : d5503 p = 1) : d138 p ≤ (0 : Int) + d2735 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d138, d2735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15090 p hg
    simpa only [d138, d2735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d138, d2735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15092 p hg
    simpa only [d138, d2735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15094 (p : Pattern) (guard : d5503 p = 1) : d139 p ≤ (0 : Int) + d2736 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d139, d2736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15083 p hg
    simpa only [d139, d2736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d139, d2736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d139, d2736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15095 (p : Pattern) (guard : d5503 p = 1) : d140 p ≤ (0 : Int) + d2737 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d140, d2737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15066 p hg
    simpa only [d140, d2737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d140, d2737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15094 p hg
    simpa only [d140, d2737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15096 (p : Pattern) (guard : d5503 p = 1) : d141 p ≤ (0 : Int) + d2738 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d141, d2738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15069 p hg
    simpa only [d141, d2738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d141, d2738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14939 p hg
    simpa only [d141, d2738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15097 (p : Pattern) (guard : d5503 p = 1) : d142 p ≤ (0 : Int) + d2739 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d142, d2739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15095 p hg
    simpa only [d142, d2739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d142, d2739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15096 p hg
    simpa only [d142, d2739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15098 (p : Pattern) (guard : d5503 p = 1) : d143 p ≤ (0 : Int) + d2740 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d143, d2740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15069 p hg
    simpa only [d143, d2740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d143, d2740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14941 p hg
    simpa only [d143, d2740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15099 (p : Pattern) (guard : d5503 p = 1) : d144 p ≤ (0 : Int) + d2741 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d144, d2741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15098 p hg
    simpa only [d144, d2741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d144, d2741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d144, d2741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15100 (p : Pattern) (guard : d5503 p = 1) : d145 p ≤ (0 : Int) + d2742 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d145, d2742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15097 p hg
    simpa only [d145, d2742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d145, d2742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15099 p hg
    simpa only [d145, d2742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15101 (p : Pattern) (guard : d5503 p = 1) : d146 p ≤ (0 : Int) + d2743 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d146, d2743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15093 p hg
    simpa only [d146, d2743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d146, d2743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15100 p hg
    simpa only [d146, d2743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15102 (p : Pattern) (guard : d5503 p = 1) : d147 p ≤ (0 : Int) + d2744 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d147, d2744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15075 p hg
    simpa only [d147, d2744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d147, d2744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15101 p hg
    simpa only [d147, d2744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15103 (p : Pattern) (guard : d5503 p = 1) : d104 p ≤ (0 : Int) + d2745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d104, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15032 p hg
    simpa only [d104, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d104, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d104, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15104 (p : Pattern) (guard : d5503 p = 1) : d105 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d105, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15039 p hg
    simpa only [d105, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d105, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15103 p hg
    simpa only [d105, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15105 (p : Pattern) (guard : d5503 p = 1) : d108 p ≤ (0 : Int) + d2747 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d108, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15046 p hg
    simpa only [d108, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d108, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d108, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15106 (p : Pattern) (guard : d5503 p = 1) : d109 p ≤ (0 : Int) + d2748 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d109, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15047 p hg
    simpa only [d109, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d109, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15105 p hg
    simpa only [d109, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15107 (p : Pattern) (guard : d5503 p = 1) : d110 p ≤ (0 : Int) + d2749 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d110, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15104 p hg
    simpa only [d110, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d110, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15106 p hg
    simpa only [d110, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15108 (p : Pattern) (guard : d5503 p = 1) : d111 p ≤ (0 : Int) + d2750 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d111, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15104 p hg
    simpa only [d111, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d111, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15107 p hg
    simpa only [d111, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15109 (p : Pattern) (guard : d5503 p = 1) : d113 p ≤ (0 : Int) + d2751 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d113, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15107 p hg
    simpa only [d113, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d113, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15054 p hg
    simpa only [d113, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15110 (p : Pattern) (guard : d5503 p = 1) : d114 p ≤ (0 : Int) + d2752 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d114, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15108 p hg
    simpa only [d114, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d114, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15109 p hg
    simpa only [d114, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15111 (p : Pattern) (guard : d5503 p = 1) : d132 p ≤ (0 : Int) + d2753 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d132, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15083 p hg
    simpa only [d132, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d132, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15060 p hg
    simpa only [d132, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15112 (p : Pattern) (guard : d0 p = 1) : d120 p ≤ (0 : Int) + d2707 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15113 (p : Pattern) (guard : d5503 p = 1) : d120 p ≤ (0 : Int) + d2707 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15062 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15112 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15114 (p : Pattern) (guard : d5503 p = 1) : d120 p ≤ (0 : Int) + d2754 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15113 p hg
    simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15064 p hg
    simpa only [d2754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15115 (p : Pattern) (guard : d5503 p = 1) : d148 p ≤ (0 : Int) + d2755 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d148, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15114 p hg
    simpa only [d148, d2755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d148, d2755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15065 p hg
    simpa only [d148, d2755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15116 (p : Pattern) (guard : d5503 p = 1) : d149 p ≤ (0 : Int) + d2756 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d149, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15111 p hg
    simpa only [d149, d2756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d149, d2756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15115 p hg
    simpa only [d149, d2756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15117 (p : Pattern) (guard : d5503 p = 1) : d150 p ≤ (0 : Int) + d2757 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d150, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15116 p hg
    simpa only [d150, d2757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d150, d2757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d150, d2757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15118 (p : Pattern) (guard : d5503 p = 1) : d151 p ≤ (0 : Int) + d2758 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d151, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15117 p hg
    simpa only [d151, d2758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d151, d2758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d151, d2758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15119 (p : Pattern) (guard : d5503 p = 1) : d152 p ≤ (0 : Int) + d2759 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d152, d2759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15110 p hg
    simpa only [d152, d2759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d152, d2759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15118 p hg
    simpa only [d152, d2759, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
