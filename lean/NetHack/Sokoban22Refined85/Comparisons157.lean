/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons156
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare21980 (p : Pattern) (guard : d5503 p = 1) : d2814 p ≤ (0 : Int) + d2424 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21977 p hg
    simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21979 p hg
    simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21981 (p : Pattern) (guard : d5503 p = 1) : d2815 p ≤ (0 : Int) + d2425 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2815, d2425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21979 p hg
    simpa only [d2815, d2425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2815, d2425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2815, d2425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21982 (p : Pattern) (guard : d5503 p = 1) : d2816 p ≤ (0 : Int) + d2426 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2816, d2426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21980 p hg
    simpa only [d2816, d2426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2816, d2426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21981 p hg
    simpa only [d2816, d2426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21983 (p : Pattern) (guard : d5503 p = 1) : d2817 p ≤ (0 : Int) + d2427 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2817, d2427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21748 p hg
    simpa only [d2817, d2427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2817, d2427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21982 p hg
    simpa only [d2817, d2427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21984 (p : Pattern) (guard : d5503 p = 1) : d2818 p ≤ (0 : Int) + d2428 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2818, d2428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21983 p hg
    simpa only [d2818, d2428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2818, d2428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2818, d2428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21985 (p : Pattern) (guard : d5503 p = 1) : d2819 p ≤ (0 : Int) + d2429 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2819, d2429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21984 p hg
    simpa only [d2819, d2429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2819, d2429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2819, d2429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21986 (p : Pattern) (guard : d5503 p = 1) : d2820 p ≤ (0 : Int) + d2430 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2820, d2430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21975 p hg
    simpa only [d2820, d2430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2820, d2430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21985 p hg
    simpa only [d2820, d2430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21987 (p : Pattern) (guard : d5503 p = 1) : d2821 p ≤ (0 : Int) + d2431 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2821, d2431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21748 p hg
    simpa only [d2821, d2431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2821, d2431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21729 p hg
    simpa only [d2821, d2431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21988 (p : Pattern) (guard : d5503 p = 1) : d2822 p ≤ (0 : Int) + d2432 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2822, d2432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21756 p hg
    simpa only [d2822, d2432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2822, d2432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21987 p hg
    simpa only [d2822, d2432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21989 (p : Pattern) (guard : d5503 p = 1) : d2823 p ≤ (0 : Int) + d2433 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2823, d2433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21988 p hg
    simpa only [d2823, d2433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2823, d2433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21772 p hg
    simpa only [d2823, d2433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21990 (p : Pattern) (guard : d5503 p = 1) : d2824 p ≤ (0 : Int) + d2434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2824, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21982 p hg
    simpa only [d2824, d2434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2824, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2824, d2434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21991 (p : Pattern) (guard : d5503 p = 1) : d2825 p ≤ (0 : Int) + d2435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2825, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21990 p hg
    simpa only [d2825, d2435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2825, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2825, d2435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21992 (p : Pattern) (guard : d5503 p = 1) : d2826 p ≤ (0 : Int) + d2436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2826, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21991 p hg
    simpa only [d2826, d2436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2826, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2826, d2436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21993 (p : Pattern) (guard : d5503 p = 1) : d2827 p ≤ (0 : Int) + d2437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2827, d2437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21989 p hg
    simpa only [d2827, d2437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2827, d2437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21992 p hg
    simpa only [d2827, d2437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21994 (p : Pattern) (guard : d5503 p = 1) : d2828 p ≤ (0 : Int) + d2438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2828, d2438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21986 p hg
    simpa only [d2828, d2438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2828, d2438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21993 p hg
    simpa only [d2828, d2438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21995 (p : Pattern) (guard : d5503 p = 1) : d2829 p ≤ (0 : Int) + d2439 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2829, d2439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21973 p hg
    simpa only [d2829, d2439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2829, d2439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21994 p hg
    simpa only [d2829, d2439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21996 (p : Pattern) (guard : d5503 p = 1) : d2830 p ≤ (0 : Int) + d2440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2830, d2440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21994 p hg
    simpa only [d2830, d2440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2830, d2440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2830, d2440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21997 (p : Pattern) (guard : d5503 p = 1) : d2831 p ≤ (0 : Int) + d2441 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2831, d2441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21995 p hg
    simpa only [d2831, d2441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2831, d2441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21996 p hg
    simpa only [d2831, d2441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21998 (p : Pattern) (guard : d5503 p = 1) : d2832 p ≤ (0 : Int) + d2442 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2832, d2442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21821 p hg
    simpa only [d2832, d2442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2832, d2442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21997 p hg
    simpa only [d2832, d2442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21999 (p : Pattern) (guard : d5503 p = 1) : d2833 p ≤ (0 : Int) + d2443 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2833, d2443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21805 p hg
    simpa only [d2833, d2443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2833, d2443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21998 p hg
    simpa only [d2833, d2443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22000 (p : Pattern) (guard : d5503 p = 1) : d2834 p ≤ (0 : Int) + d2444 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2834, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21857 p hg
    simpa only [d2834, d2444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2834, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2834, d2444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22001 (p : Pattern) (guard : d5503 p = 1) : d2835 p ≤ (0 : Int) + d2445 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2835, d2445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21891 p hg
    simpa only [d2835, d2445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2835, d2445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22000 p hg
    simpa only [d2835, d2445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22002 (p : Pattern) (guard : d5503 p = 1) : d2836 p ≤ (0 : Int) + d2446 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2836, d2446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22000 p hg
    simpa only [d2836, d2446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2836, d2446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2836, d2446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22003 (p : Pattern) (guard : d5503 p = 1) : d2837 p ≤ (0 : Int) + d2447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2837, d2447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22001 p hg
    simpa only [d2837, d2447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2837, d2447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22002 p hg
    simpa only [d2837, d2447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22004 (p : Pattern) (guard : d5503 p = 1) : d2838 p ≤ (0 : Int) + d2448 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2838, d2448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21873 p hg
    simpa only [d2838, d2448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2838, d2448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2838, d2448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22005 (p : Pattern) (guard : d5503 p = 1) : d2839 p ≤ (0 : Int) + d2449 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2839, d2449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21898 p hg
    simpa only [d2839, d2449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2839, d2449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22004 p hg
    simpa only [d2839, d2449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22006 (p : Pattern) (guard : d5503 p = 1) : d2840 p ≤ (0 : Int) + d2450 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2840, d2450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22004 p hg
    simpa only [d2840, d2450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2840, d2450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2840, d2450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22007 (p : Pattern) (guard : d5503 p = 1) : d2841 p ≤ (0 : Int) + d2451 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2841, d2451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22005 p hg
    simpa only [d2841, d2451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2841, d2451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22006 p hg
    simpa only [d2841, d2451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22008 (p : Pattern) (guard : d5503 p = 1) : d2842 p ≤ (0 : Int) + d2452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2842, d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22003 p hg
    simpa only [d2842, d2452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2842, d2452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22007 p hg
    simpa only [d2842, d2452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22009 (p : Pattern) (guard : d5503 p = 1) : d2843 p ≤ (0 : Int) + d2453 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2843, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21879 p hg
    simpa only [d2843, d2453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2843, d2453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22008 p hg
    simpa only [d2843, d2453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22010 (p : Pattern) (guard : d5503 p = 1) : d2844 p ≤ (0 : Int) + d2444 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2844, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21909 p hg
    simpa only [d2844, d2444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2844, d2444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2844, d2444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22011 (p : Pattern) (guard : d5503 p = 1) : d2845 p ≤ (0 : Int) + d2454 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2845, d2454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21923 p hg
    simpa only [d2845, d2454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2845, d2454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22010 p hg
    simpa only [d2845, d2454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22012 (p : Pattern) (guard : d5503 p = 1) : d2846 p ≤ (0 : Int) + d2446 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2846, d2446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22010 p hg
    simpa only [d2846, d2446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2846, d2446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2846, d2446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22013 (p : Pattern) (guard : d5503 p = 1) : d2847 p ≤ (0 : Int) + d2455 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2847, d2455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22011 p hg
    simpa only [d2847, d2455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2847, d2455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22012 p hg
    simpa only [d2847, d2455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22014 (p : Pattern) (guard : d5503 p = 1) : d2848 p ≤ (0 : Int) + d2456 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2848, d2456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22013 p hg
    simpa only [d2848, d2456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2848, d2456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21931 p hg
    simpa only [d2848, d2456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22015 (p : Pattern) (guard : d5503 p = 1) : d2849 p ≤ (0 : Int) + d2457 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2849, d2457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21922 p hg
    simpa only [d2849, d2457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2849, d2457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22014 p hg
    simpa only [d2849, d2457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22016 (p : Pattern) (guard : d5503 p = 1) : d2850 p ≤ (0 : Int) + d2458 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2850, d2458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22009 p hg
    simpa only [d2850, d2458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2850, d2458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22015 p hg
    simpa only [d2850, d2458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22017 (p : Pattern) (guard : d5503 p = 1) : d2851 p ≤ (0 : Int) + d2459 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2851, d2459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22015 p hg
    simpa only [d2851, d2459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2851, d2459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21938 p hg
    simpa only [d2851, d2459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22018 (p : Pattern) (guard : d5503 p = 1) : d2852 p ≤ (0 : Int) + d2460 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2852, d2460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22016 p hg
    simpa only [d2852, d2460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2852, d2460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22017 p hg
    simpa only [d2852, d2460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22019 (p : Pattern) (guard : d5503 p = 1) : d2746 p ≤ (0 : Int) + d2325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2746, d2325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21842 p hg
    simpa only [d2746, d2325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2746, d2325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21906 p hg
    simpa only [d2746, d2325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22020 (p : Pattern) (guard : d5503 p = 1) : d2746 p ≤ (0 : Int) + d2392 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22019 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21907 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22021 (p : Pattern) (guard : d5503 p = 1) : d2750 p ≤ (0 : Int) + d2393 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2750, d2393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22020 p hg
    simpa only [d2750, d2393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2750, d2393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21910 p hg
    simpa only [d2750, d2393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22022 (p : Pattern) (guard : d5503 p = 1) : d2752 p ≤ (0 : Int) + d2394 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2752, d2394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22021 p hg
    simpa only [d2752, d2394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2752, d2394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21912 p hg
    simpa only [d2752, d2394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22023 (p : Pattern) (guard : d5503 p = 1) : d2853 p ≤ (0 : Int) + d2461 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2853, d2461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21886 p hg
    simpa only [d2853, d2461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2853, d2461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21869 p hg
    simpa only [d2853, d2461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22024 (p : Pattern) (guard : d5503 p = 1) : d2854 p ≤ (0 : Int) + d2462 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2854, d2462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21914 p hg
    simpa only [d2854, d2462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2854, d2462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22023 p hg
    simpa only [d2854, d2462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22025 (p : Pattern) (guard : d5503 p = 1) : d2855 p ≤ (0 : Int) + d2463 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2855, d2463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22024 p hg
    simpa only [d2855, d2463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2855, d2463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22004 p hg
    simpa only [d2855, d2463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22026 (p : Pattern) (guard : d5503 p = 1) : d2856 p ≤ (0 : Int) + d2464 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2856, d2464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21917 p hg
    simpa only [d2856, d2464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2856, d2464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2856, d2464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22027 (p : Pattern) (guard : d5503 p = 1) : d2857 p ≤ (0 : Int) + d2465 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2857, d2465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22026 p hg
    simpa only [d2857, d2465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2857, d2465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2857, d2465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22028 (p : Pattern) (guard : d5503 p = 1) : d2858 p ≤ (0 : Int) + d2466 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2858, d2466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22027 p hg
    simpa only [d2858, d2466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2858, d2466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2858, d2466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22029 (p : Pattern) (guard : d5503 p = 1) : d2859 p ≤ (0 : Int) + d2467 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2859, d2467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22025 p hg
    simpa only [d2859, d2467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2859, d2467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22028 p hg
    simpa only [d2859, d2467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22030 (p : Pattern) (guard : d5503 p = 1) : d2860 p ≤ (0 : Int) + d2468 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2860, d2468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22022 p hg
    simpa only [d2860, d2468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2860, d2468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22029 p hg
    simpa only [d2860, d2468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22031 (p : Pattern) (guard : d5503 p = 1) : d2861 p ≤ (0 : Int) + d2469 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2861, d2469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21853 p hg
    simpa only [d2861, d2469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2861, d2469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21869 p hg
    simpa only [d2861, d2469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22032 (p : Pattern) (guard : d5503 p = 1) : d2862 p ≤ (0 : Int) + d2470 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2862, d2470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22031 p hg
    simpa only [d2862, d2470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2862, d2470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21873 p hg
    simpa only [d2862, d2470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22033 (p : Pattern) (guard : d5503 p = 1) : d2863 p ≤ (0 : Int) + d2471 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2863, d2471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22032 p hg
    simpa only [d2863, d2471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2863, d2471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22027 p hg
    simpa only [d2863, d2471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22034 (p : Pattern) (guard : d5503 p = 1) : d2864 p ≤ (0 : Int) + d2472 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2864, d2472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21700 p hg
    simpa only [d2864, d2472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2864, d2472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2864, d2472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22035 (p : Pattern) (guard : d5503 p = 1) : d2865 p ≤ (0 : Int) + d2473 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2865, d2473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22033 p hg
    simpa only [d2865, d2473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2865, d2473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22034 p hg
    simpa only [d2865, d2473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22036 (p : Pattern) (guard : d5503 p = 1) : d2866 p ≤ (0 : Int) + d2474 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2866, d2474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22013 p hg
    simpa only [d2866, d2474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2866, d2474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22035 p hg
    simpa only [d2866, d2474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22037 (p : Pattern) (guard : d5503 p = 1) : d2867 p ≤ (0 : Int) + d2475 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2867, d2475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22030 p hg
    simpa only [d2867, d2475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2867, d2475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22036 p hg
    simpa only [d2867, d2475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22038 (p : Pattern) (guard : d5503 p = 1) : d2868 p ≤ (0 : Int) + d2476 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2868, d2476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21914 p hg
    simpa only [d2868, d2476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2868, d2476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21729 p hg
    simpa only [d2868, d2476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22039 (p : Pattern) (guard : d5503 p = 1) : d2869 p ≤ (0 : Int) + d2477 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2869, d2477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21907 p hg
    simpa only [d2869, d2477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2869, d2477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22038 p hg
    simpa only [d2869, d2477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22040 (p : Pattern) (guard : d5503 p = 1) : d2870 p ≤ (0 : Int) + d2478 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2870, d2478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22039 p hg
    simpa only [d2870, d2478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2870, d2478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21927 p hg
    simpa only [d2870, d2478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22041 (p : Pattern) (guard : d5503 p = 1) : d2871 p ≤ (0 : Int) + d2479 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2871, d2479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22040 p hg
    simpa only [d2871, d2479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2871, d2479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21931 p hg
    simpa only [d2871, d2479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22042 (p : Pattern) (guard : d5503 p = 1) : d2872 p ≤ (0 : Int) + d2480 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2872, d2480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21914 p hg
    simpa only [d2872, d2480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2872, d2480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22010 p hg
    simpa only [d2872, d2480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22043 (p : Pattern) (guard : d5503 p = 1) : d2873 p ≤ (0 : Int) + d2481 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2873, d2481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22042 p hg
    simpa only [d2873, d2481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2873, d2481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21930 p hg
    simpa only [d2873, d2481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22044 (p : Pattern) (guard : d5503 p = 1) : d2874 p ≤ (0 : Int) + d2482 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2874, d2482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21753 p hg
    simpa only [d2874, d2482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2874, d2482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2874, d2482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22045 (p : Pattern) (guard : d5503 p = 1) : d2875 p ≤ (0 : Int) + d2483 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2875, d2483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22044 p hg
    simpa only [d2875, d2483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2875, d2483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2875, d2483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22046 (p : Pattern) (guard : d5503 p = 1) : d2876 p ≤ (0 : Int) + d2484 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2876, d2484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22043 p hg
    simpa only [d2876, d2484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2876, d2484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22045 p hg
    simpa only [d2876, d2484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22047 (p : Pattern) (guard : d5503 p = 1) : d2877 p ≤ (0 : Int) + d2485 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2877, d2485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22041 p hg
    simpa only [d2877, d2485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2877, d2485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22046 p hg
    simpa only [d2877, d2485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22048 (p : Pattern) (guard : d5503 p = 1) : d2878 p ≤ (0 : Int) + d2486 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2878, d2486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22037 p hg
    simpa only [d2878, d2486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2878, d2486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22047 p hg
    simpa only [d2878, d2486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22049 (p : Pattern) (guard : d5503 p = 1) : d2879 p ≤ (0 : Int) + d2487 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2879, d2487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21914 p hg
    simpa only [d2879, d2487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2879, d2487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21752 p hg
    simpa only [d2879, d2487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22050 (p : Pattern) (guard : d5503 p = 1) : d2880 p ≤ (0 : Int) + d2488 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2880, d2488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21907 p hg
    simpa only [d2880, d2488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2880, d2488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22049 p hg
    simpa only [d2880, d2488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22051 (p : Pattern) (guard : d5503 p = 1) : d2881 p ≤ (0 : Int) + d2489 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2881, d2489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21909 p hg
    simpa only [d2881, d2489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2881, d2489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21752 p hg
    simpa only [d2881, d2489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22052 (p : Pattern) (guard : d5503 p = 1) : d2882 p ≤ (0 : Int) + d2490 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2882, d2490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22051 p hg
    simpa only [d2882, d2490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2882, d2490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2882, d2490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22053 (p : Pattern) (guard : d5503 p = 1) : d2883 p ≤ (0 : Int) + d2491 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2883, d2491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22050 p hg
    simpa only [d2883, d2491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2883, d2491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22052 p hg
    simpa only [d2883, d2491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22054 (p : Pattern) (guard : d5503 p = 1) : d2884 p ≤ (0 : Int) + d2492 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2884, d2492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21918 p hg
    simpa only [d2884, d2492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2884, d2492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21729 p hg
    simpa only [d2884, d2492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22055 (p : Pattern) (guard : d5503 p = 1) : d2885 p ≤ (0 : Int) + d2493 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2885, d2493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22054 p hg
    simpa only [d2885, d2493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2885, d2493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2885, d2493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22056 (p : Pattern) (guard : d5503 p = 1) : d2886 p ≤ (0 : Int) + d2494 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2886, d2494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22055 p hg
    simpa only [d2886, d2494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2886, d2494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2886, d2494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22057 (p : Pattern) (guard : d5503 p = 1) : d2887 p ≤ (0 : Int) + d2495 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2887, d2495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22053 p hg
    simpa only [d2887, d2495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2887, d2495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22056 p hg
    simpa only [d2887, d2495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22058 (p : Pattern) (guard : d5503 p = 1) : d2888 p ≤ (0 : Int) + d2496 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2888, d2496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22057 p hg
    simpa only [d2888, d2496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2888, d2496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22046 p hg
    simpa only [d2888, d2496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22059 (p : Pattern) (guard : d5503 p = 1) : d2889 p ≤ (0 : Int) + d2497 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2889, d2497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22058 p hg
    simpa only [d2889, d2497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2889, d2497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2889, d2497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22060 (p : Pattern) (guard : d5503 p = 1) : d2890 p ≤ (0 : Int) + d2498 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2890, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22048 p hg
    simpa only [d2890, d2498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2890, d2498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22059 p hg
    simpa only [d2890, d2498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22061 (p : Pattern) (guard : d5503 p = 1) : d2891 p ≤ (0 : Int) + d2499 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2891, d2499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22018 p hg
    simpa only [d2891, d2499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2891, d2499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22060 p hg
    simpa only [d2891, d2499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22062 (p : Pattern) (guard : d5503 p = 1) : d2892 p ≤ (0 : Int) + d2500 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2892, d2500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21805 p hg
    simpa only [d2892, d2500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2892, d2500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22061 p hg
    simpa only [d2892, d2500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22063 (p : Pattern) (guard : d5503 p = 1) : d2893 p ≤ (0 : Int) + d2501 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2893, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21999 p hg
    simpa only [d2893, d2501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2893, d2501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22062 p hg
    simpa only [d2893, d2501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22064 (p : Pattern) (guard : d5503 p = 1) : d2894 p ≤ (0 : Int) + d2502 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2894, d2502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21955 p hg
    simpa only [d2894, d2502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2894, d2502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22063 p hg
    simpa only [d2894, d2502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22065 (p : Pattern) (guard : d0 p = 1) : d2503 p ≤ (4 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22066 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22067 (p : Pattern) (guard : d5502 p = 1) : d2504 p ≤ (4 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2507 p hg
    simpa only [d5502, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22066 p hg
    simpa only [d5502, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22068 (p : Pattern) (guard : d5538 p = 1) : d2505 p ≤ (4 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22065 p hg
    simpa only [d5538, d2505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22067 p hg
    simpa only [d5538, d2505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22069 (p : Pattern) (guard : d0 p = 1) : d2504 p ≤ (4 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22070 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (4 : Int) + d0 p := by
  omega
theorem compare22071 (p : Pattern) (guard : d1 p = 1) : d1769 p ≤ (4 : Int) + d0 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22070 p hg
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2508 p hg
    simpa only [d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22072 (p : Pattern) (guard : d1 p = 1) : d1770 p ≤ (4 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1770, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22071 p hg
    simpa only [d1770, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1770, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2510 p hg
    simpa only [d1770, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22073 (p : Pattern) (guard : d5502 p = 1) : d2506 p ≤ (4 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22072 p hg
    simpa only [d5502, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22066 p hg
    simpa only [d5502, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22074 (p : Pattern) (guard : d5538 p = 1) : d2507 p ≤ (4 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22069 p hg
    simpa only [d5538, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22073 p hg
    simpa only [d5538, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22075 (p : Pattern) (guard : d5538 p = 1) : d2508 p ≤ (4 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22068 p hg
    simpa only [d2508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22074 p hg
    simpa only [d2508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22076 (p : Pattern) (guard : d1 p = 1) : d1683 p ≤ (4 : Int) + d0 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22070 p hg
    simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2641 p hg
    simpa only [d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22077 (p : Pattern) (guard : d1 p = 1) : d1684 p ≤ (4 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1684, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22076 p hg
    simpa only [d1684, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1684, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2642 p hg
    simpa only [d1684, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22078 (p : Pattern) (guard : d5502 p = 1) : d2509 p ≤ (4 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22077 p hg
    simpa only [d5502, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22066 p hg
    simpa only [d5502, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22079 (p : Pattern) (guard : d5538 p = 1) : d2510 p ≤ (4 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22069 p hg
    simpa only [d5538, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22078 p hg
    simpa only [d5538, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22080 (p : Pattern) (guard : d5538 p = 1) : d12 p ≤ (4 : Int) + d12 p := by
  omega
theorem compare22081 (p : Pattern) (guard : d5538 p = 1) : d2511 p ≤ (4 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2511, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22079 p hg
    simpa only [d2511, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2511, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2511, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22082 (p : Pattern) (guard : d5538 p = 1) : d2512 p ≤ (4 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2512, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22075 p hg
    simpa only [d2512, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2512, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22081 p hg
    simpa only [d2512, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22083 (p : Pattern) (guard : d0 p = 1) : d2513 p ≤ (4 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22084 (p : Pattern) (guard : d5538 p = 1) : d2514 p ≤ (4 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22083 p hg
    simpa only [d5538, d2514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22067 p hg
    simpa only [d5538, d2514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22085 (p : Pattern) (guard : d5538 p = 1) : d2515 p ≤ (4 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22084 p hg
    simpa only [d2515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22074 p hg
    simpa only [d2515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22086 (p : Pattern) (guard : d5538 p = 1) : d2516 p ≤ (4 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2516, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22085 p hg
    simpa only [d2516, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2516, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22081 p hg
    simpa only [d2516, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22087 (p : Pattern) (guard : d5538 p = 1) : d2517 p ≤ (4 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22082 p hg
    simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22086 p hg
    simpa only [d2517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22088 (p : Pattern) (guard : d5538 p = 1) : d2504 p ≤ (4 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22069 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22067 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22089 (p : Pattern) (guard : d5538 p = 1) : d2518 p ≤ (4 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22088 p hg
    simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22074 p hg
    simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22090 (p : Pattern) (guard : d5538 p = 1) : d2519 p ≤ (4 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2519, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22089 p hg
    simpa only [d2519, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2519, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22081 p hg
    simpa only [d2519, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22091 (p : Pattern) (guard : d0 p = 1) : d2520 p ≤ (4 : Int) + d18 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22092 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d18 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22093 (p : Pattern) (guard : d5502 p = 1) : d2520 p ≤ (4 : Int) + d18 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2529 p hg
    simpa only [d5502, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22092 p hg
    simpa only [d5502, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22094 (p : Pattern) (guard : d5538 p = 1) : d2520 p ≤ (4 : Int) + d18 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22091 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22093 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22095 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (4 : Int) + d4 p := by
  omega
theorem compare22096 (p : Pattern) (guard : d1 p = 1) : d1794 p ≤ (4 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22095 p hg
    simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22097 (p : Pattern) (guard : d1 p = 1) : d1795 p ≤ (4 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1795, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22096 p hg
    simpa only [d1795, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1795, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2531 p hg
    simpa only [d1795, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22098 (p : Pattern) (guard : d5502 p = 1) : d2521 p ≤ (4 : Int) + d18 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22097 p hg
    simpa only [d5502, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22092 p hg
    simpa only [d5502, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22099 (p : Pattern) (guard : d5538 p = 1) : d2522 p ≤ (4 : Int) + d18 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22091 p hg
    simpa only [d5538, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22098 p hg
    simpa only [d5538, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22100 (p : Pattern) (guard : d5538 p = 1) : d2523 p ≤ (4 : Int) + d18 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22094 p hg
    simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22099 p hg
    simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22101 (p : Pattern) (guard : d1 p = 1) : d1693 p ≤ (4 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22095 p hg
    simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2646 p hg
    simpa only [d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22102 (p : Pattern) (guard : d1 p = 1) : d1694 p ≤ (4 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1694, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22101 p hg
    simpa only [d1694, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1694, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2647 p hg
    simpa only [d1694, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22103 (p : Pattern) (guard : d5502 p = 1) : d2524 p ≤ (4 : Int) + d18 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22102 p hg
    simpa only [d5502, d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22092 p hg
    simpa only [d5502, d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22104 (p : Pattern) (guard : d5538 p = 1) : d2525 p ≤ (4 : Int) + d18 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22091 p hg
    simpa only [d5538, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22103 p hg
    simpa only [d5538, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22105 (p : Pattern) (guard : d5538 p = 1) : d2526 p ≤ (4 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2526, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22104 p hg
    simpa only [d2526, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2526, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22080 p hg
    simpa only [d2526, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22106 (p : Pattern) (guard : d5538 p = 1) : d2527 p ≤ (4 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2527, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22100 p hg
    simpa only [d2527, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2527, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22105 p hg
    simpa only [d2527, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22107 (p : Pattern) (guard : d5538 p = 1) : d2528 p ≤ (4 : Int) + d21 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2528, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22090 p hg
    simpa only [d2528, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2528, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22106 p hg
    simpa only [d2528, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22108 (p : Pattern) (guard : d5538 p = 1) : d2529 p ≤ (4 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2529, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22087 p hg
    simpa only [d2529, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2529, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22107 p hg
    simpa only [d2529, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22109 (p : Pattern) (guard : d0 p = 1) : d2530 p ≤ (4 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22110 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (4 : Int) + d24 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare22111 (p : Pattern) (guard : d5502 p = 1) : d2530 p ≤ (4 : Int) + d24 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2539 p hg
    simpa only [d5502, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22110 p hg
    simpa only [d5502, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22112 (p : Pattern) (guard : d5538 p = 1) : d2530 p ≤ (4 : Int) + d24 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22109 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22111 p hg
    simpa only [d5538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22113 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (4 : Int) + d9 p := by
  omega
theorem compare22114 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (4 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22113 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2540 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22115 (p : Pattern) (guard : d1 p = 1) : d356 p ≤ (4 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d356, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22114 p hg
    simpa only [d356, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d356, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2541 p hg
    simpa only [d356, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22116 (p : Pattern) (guard : d5502 p = 1) : d357 p ≤ (4 : Int) + d24 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22115 p hg
    simpa only [d5502, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22110 p hg
    simpa only [d5502, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22117 (p : Pattern) (guard : d5538 p = 1) : d2531 p ≤ (4 : Int) + d24 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5538, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22109 p hg
    simpa only [d5538, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d5538, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22116 p hg
    simpa only [d5538, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22118 (p : Pattern) (guard : d5538 p = 1) : d2532 p ≤ (4 : Int) + d24 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5538 p = 1 := by simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22112 p hg
    simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5538 p = 1 := by simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22117 p hg
    simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22119 (p : Pattern) (guard : d1 p = 1) : d1701 p ≤ (4 : Int) + d9 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22113 p hg
    simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2653 p hg
    simpa only [d1701, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
