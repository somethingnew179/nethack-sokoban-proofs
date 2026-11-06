/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons137
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare19320 (p : Pattern) (guard : d5503 p = 1) : d2428 p ≤ (0 : Int) + d2818 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2428, d2818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19319 p hg
    simpa only [d2428, d2818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2428, d2818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2428, d2818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19321 (p : Pattern) (guard : d5503 p = 1) : d2429 p ≤ (0 : Int) + d2819 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2429, d2819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19320 p hg
    simpa only [d2429, d2819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2429, d2819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2429, d2819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19322 (p : Pattern) (guard : d5503 p = 1) : d2430 p ≤ (0 : Int) + d2820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2430, d2820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19311 p hg
    simpa only [d2430, d2820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2430, d2820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19321 p hg
    simpa only [d2430, d2820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19323 (p : Pattern) (guard : d5503 p = 1) : d2431 p ≤ (0 : Int) + d2821 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2431, d2821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19084 p hg
    simpa only [d2431, d2821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2431, d2821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19065 p hg
    simpa only [d2431, d2821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19324 (p : Pattern) (guard : d5503 p = 1) : d2432 p ≤ (0 : Int) + d2822 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2432, d2822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19092 p hg
    simpa only [d2432, d2822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2432, d2822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19323 p hg
    simpa only [d2432, d2822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19325 (p : Pattern) (guard : d5503 p = 1) : d2433 p ≤ (0 : Int) + d2823 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2433, d2823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19324 p hg
    simpa only [d2433, d2823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2433, d2823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19108 p hg
    simpa only [d2433, d2823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19326 (p : Pattern) (guard : d5503 p = 1) : d2434 p ≤ (0 : Int) + d2824 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2434, d2824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19318 p hg
    simpa only [d2434, d2824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2434, d2824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2434, d2824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19327 (p : Pattern) (guard : d5503 p = 1) : d2435 p ≤ (0 : Int) + d2825 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2435, d2825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19326 p hg
    simpa only [d2435, d2825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2435, d2825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2435, d2825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19328 (p : Pattern) (guard : d5503 p = 1) : d2436 p ≤ (0 : Int) + d2826 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2436, d2826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19327 p hg
    simpa only [d2436, d2826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2436, d2826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2436, d2826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19329 (p : Pattern) (guard : d5503 p = 1) : d2437 p ≤ (0 : Int) + d2827 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2437, d2827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19325 p hg
    simpa only [d2437, d2827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2437, d2827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19328 p hg
    simpa only [d2437, d2827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19330 (p : Pattern) (guard : d5503 p = 1) : d2438 p ≤ (0 : Int) + d2828 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2438, d2828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19322 p hg
    simpa only [d2438, d2828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2438, d2828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19329 p hg
    simpa only [d2438, d2828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19331 (p : Pattern) (guard : d5503 p = 1) : d2439 p ≤ (0 : Int) + d2829 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2439, d2829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19309 p hg
    simpa only [d2439, d2829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2439, d2829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19330 p hg
    simpa only [d2439, d2829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19332 (p : Pattern) (guard : d5503 p = 1) : d2440 p ≤ (0 : Int) + d2830 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2440, d2830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19330 p hg
    simpa only [d2440, d2830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2440, d2830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2440, d2830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19333 (p : Pattern) (guard : d5503 p = 1) : d2441 p ≤ (0 : Int) + d2831 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2441, d2831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19331 p hg
    simpa only [d2441, d2831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2441, d2831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19332 p hg
    simpa only [d2441, d2831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19334 (p : Pattern) (guard : d5503 p = 1) : d2442 p ≤ (0 : Int) + d2832 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2442, d2832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19157 p hg
    simpa only [d2442, d2832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2442, d2832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19333 p hg
    simpa only [d2442, d2832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19335 (p : Pattern) (guard : d5503 p = 1) : d2443 p ≤ (0 : Int) + d2833 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2443, d2833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19141 p hg
    simpa only [d2443, d2833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2443, d2833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19334 p hg
    simpa only [d2443, d2833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19336 (p : Pattern) (guard : d5503 p = 1) : d2444 p ≤ (0 : Int) + d2834 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2444, d2834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19193 p hg
    simpa only [d2444, d2834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2444, d2834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2444, d2834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19337 (p : Pattern) (guard : d5503 p = 1) : d2445 p ≤ (0 : Int) + d2835 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2445, d2835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19227 p hg
    simpa only [d2445, d2835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2445, d2835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19336 p hg
    simpa only [d2445, d2835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19338 (p : Pattern) (guard : d5503 p = 1) : d2446 p ≤ (0 : Int) + d2836 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2446, d2836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19336 p hg
    simpa only [d2446, d2836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2446, d2836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2446, d2836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19339 (p : Pattern) (guard : d5503 p = 1) : d2447 p ≤ (0 : Int) + d2837 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2447, d2837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19337 p hg
    simpa only [d2447, d2837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2447, d2837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19338 p hg
    simpa only [d2447, d2837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19340 (p : Pattern) (guard : d5503 p = 1) : d2448 p ≤ (0 : Int) + d2838 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2448, d2838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19209 p hg
    simpa only [d2448, d2838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2448, d2838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2448, d2838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19341 (p : Pattern) (guard : d5503 p = 1) : d2449 p ≤ (0 : Int) + d2839 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2449, d2839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19234 p hg
    simpa only [d2449, d2839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2449, d2839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19340 p hg
    simpa only [d2449, d2839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19342 (p : Pattern) (guard : d5503 p = 1) : d2450 p ≤ (0 : Int) + d2840 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2450, d2840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19340 p hg
    simpa only [d2450, d2840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2450, d2840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2450, d2840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19343 (p : Pattern) (guard : d5503 p = 1) : d2451 p ≤ (0 : Int) + d2841 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2451, d2841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19341 p hg
    simpa only [d2451, d2841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2451, d2841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19342 p hg
    simpa only [d2451, d2841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19344 (p : Pattern) (guard : d5503 p = 1) : d2452 p ≤ (0 : Int) + d2842 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2452, d2842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19339 p hg
    simpa only [d2452, d2842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2452, d2842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19343 p hg
    simpa only [d2452, d2842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19345 (p : Pattern) (guard : d5503 p = 1) : d2453 p ≤ (0 : Int) + d2843 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2453, d2843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19215 p hg
    simpa only [d2453, d2843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2453, d2843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19344 p hg
    simpa only [d2453, d2843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19346 (p : Pattern) (guard : d5503 p = 1) : d2444 p ≤ (0 : Int) + d2844 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2444, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19245 p hg
    simpa only [d2444, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2444, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2444, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19347 (p : Pattern) (guard : d5503 p = 1) : d2454 p ≤ (0 : Int) + d2845 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2454, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19259 p hg
    simpa only [d2454, d2845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2454, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19346 p hg
    simpa only [d2454, d2845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19348 (p : Pattern) (guard : d5503 p = 1) : d2446 p ≤ (0 : Int) + d2846 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2446, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19346 p hg
    simpa only [d2446, d2846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2446, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2446, d2846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19349 (p : Pattern) (guard : d5503 p = 1) : d2455 p ≤ (0 : Int) + d2847 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2455, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19347 p hg
    simpa only [d2455, d2847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2455, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19348 p hg
    simpa only [d2455, d2847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19350 (p : Pattern) (guard : d5503 p = 1) : d2456 p ≤ (0 : Int) + d2848 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2456, d2848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19349 p hg
    simpa only [d2456, d2848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2456, d2848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19267 p hg
    simpa only [d2456, d2848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19351 (p : Pattern) (guard : d5503 p = 1) : d2457 p ≤ (0 : Int) + d2849 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2457, d2849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19258 p hg
    simpa only [d2457, d2849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2457, d2849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19350 p hg
    simpa only [d2457, d2849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19352 (p : Pattern) (guard : d5503 p = 1) : d2458 p ≤ (0 : Int) + d2850 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2458, d2850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19345 p hg
    simpa only [d2458, d2850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2458, d2850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19351 p hg
    simpa only [d2458, d2850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19353 (p : Pattern) (guard : d5503 p = 1) : d2459 p ≤ (0 : Int) + d2851 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2459, d2851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19351 p hg
    simpa only [d2459, d2851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2459, d2851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19274 p hg
    simpa only [d2459, d2851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19354 (p : Pattern) (guard : d5503 p = 1) : d2460 p ≤ (0 : Int) + d2852 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2460, d2852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19352 p hg
    simpa only [d2460, d2852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2460, d2852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19353 p hg
    simpa only [d2460, d2852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19355 (p : Pattern) (guard : d5503 p = 1) : d2325 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2325, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19178 p hg
    simpa only [d2325, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2325, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19242 p hg
    simpa only [d2325, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19356 (p : Pattern) (guard : d5503 p = 1) : d2392 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19355 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19243 p hg
    simpa only [d2392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19357 (p : Pattern) (guard : d5503 p = 1) : d2393 p ≤ (0 : Int) + d2750 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2393, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19356 p hg
    simpa only [d2393, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2393, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19246 p hg
    simpa only [d2393, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19358 (p : Pattern) (guard : d5503 p = 1) : d2394 p ≤ (0 : Int) + d2752 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2394, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19357 p hg
    simpa only [d2394, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2394, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19248 p hg
    simpa only [d2394, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19359 (p : Pattern) (guard : d5503 p = 1) : d2461 p ≤ (0 : Int) + d2853 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2461, d2853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19222 p hg
    simpa only [d2461, d2853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2461, d2853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19205 p hg
    simpa only [d2461, d2853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19360 (p : Pattern) (guard : d5503 p = 1) : d2462 p ≤ (0 : Int) + d2854 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2462, d2854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19250 p hg
    simpa only [d2462, d2854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2462, d2854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19359 p hg
    simpa only [d2462, d2854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19361 (p : Pattern) (guard : d5503 p = 1) : d2463 p ≤ (0 : Int) + d2855 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2463, d2855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19360 p hg
    simpa only [d2463, d2855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2463, d2855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19340 p hg
    simpa only [d2463, d2855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19362 (p : Pattern) (guard : d5503 p = 1) : d2464 p ≤ (0 : Int) + d2856 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2464, d2856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19253 p hg
    simpa only [d2464, d2856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2464, d2856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2464, d2856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19363 (p : Pattern) (guard : d5503 p = 1) : d2465 p ≤ (0 : Int) + d2857 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2465, d2857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19362 p hg
    simpa only [d2465, d2857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2465, d2857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2465, d2857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19364 (p : Pattern) (guard : d5503 p = 1) : d2466 p ≤ (0 : Int) + d2858 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2466, d2858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19363 p hg
    simpa only [d2466, d2858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2466, d2858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2466, d2858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19365 (p : Pattern) (guard : d5503 p = 1) : d2467 p ≤ (0 : Int) + d2859 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2467, d2859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19361 p hg
    simpa only [d2467, d2859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2467, d2859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19364 p hg
    simpa only [d2467, d2859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19366 (p : Pattern) (guard : d5503 p = 1) : d2468 p ≤ (0 : Int) + d2860 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2468, d2860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19358 p hg
    simpa only [d2468, d2860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2468, d2860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19365 p hg
    simpa only [d2468, d2860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19367 (p : Pattern) (guard : d5503 p = 1) : d2469 p ≤ (0 : Int) + d2861 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2469, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19189 p hg
    simpa only [d2469, d2861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2469, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19205 p hg
    simpa only [d2469, d2861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19368 (p : Pattern) (guard : d5503 p = 1) : d2470 p ≤ (0 : Int) + d2862 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2470, d2862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19367 p hg
    simpa only [d2470, d2862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2470, d2862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19209 p hg
    simpa only [d2470, d2862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19369 (p : Pattern) (guard : d5503 p = 1) : d2471 p ≤ (0 : Int) + d2863 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2471, d2863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19368 p hg
    simpa only [d2471, d2863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2471, d2863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19363 p hg
    simpa only [d2471, d2863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19370 (p : Pattern) (guard : d5503 p = 1) : d2472 p ≤ (0 : Int) + d2864 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2472, d2864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19036 p hg
    simpa only [d2472, d2864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2472, d2864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2472, d2864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19371 (p : Pattern) (guard : d5503 p = 1) : d2473 p ≤ (0 : Int) + d2865 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2473, d2865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19369 p hg
    simpa only [d2473, d2865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2473, d2865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19370 p hg
    simpa only [d2473, d2865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19372 (p : Pattern) (guard : d5503 p = 1) : d2474 p ≤ (0 : Int) + d2866 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2474, d2866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19349 p hg
    simpa only [d2474, d2866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2474, d2866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19371 p hg
    simpa only [d2474, d2866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19373 (p : Pattern) (guard : d5503 p = 1) : d2475 p ≤ (0 : Int) + d2867 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2475, d2867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19366 p hg
    simpa only [d2475, d2867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2475, d2867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19372 p hg
    simpa only [d2475, d2867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19374 (p : Pattern) (guard : d5503 p = 1) : d2476 p ≤ (0 : Int) + d2868 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2476, d2868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19250 p hg
    simpa only [d2476, d2868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2476, d2868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19065 p hg
    simpa only [d2476, d2868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19375 (p : Pattern) (guard : d5503 p = 1) : d2477 p ≤ (0 : Int) + d2869 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2477, d2869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19243 p hg
    simpa only [d2477, d2869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2477, d2869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19374 p hg
    simpa only [d2477, d2869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19376 (p : Pattern) (guard : d5503 p = 1) : d2478 p ≤ (0 : Int) + d2870 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2478, d2870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19375 p hg
    simpa only [d2478, d2870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2478, d2870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19263 p hg
    simpa only [d2478, d2870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19377 (p : Pattern) (guard : d5503 p = 1) : d2479 p ≤ (0 : Int) + d2871 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2479, d2871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19376 p hg
    simpa only [d2479, d2871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2479, d2871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19267 p hg
    simpa only [d2479, d2871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19378 (p : Pattern) (guard : d5503 p = 1) : d2480 p ≤ (0 : Int) + d2872 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2480, d2872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19250 p hg
    simpa only [d2480, d2872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2480, d2872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19346 p hg
    simpa only [d2480, d2872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19379 (p : Pattern) (guard : d5503 p = 1) : d2481 p ≤ (0 : Int) + d2873 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2481, d2873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19378 p hg
    simpa only [d2481, d2873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2481, d2873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19266 p hg
    simpa only [d2481, d2873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19380 (p : Pattern) (guard : d5503 p = 1) : d2482 p ≤ (0 : Int) + d2874 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2482, d2874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19089 p hg
    simpa only [d2482, d2874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2482, d2874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2482, d2874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19381 (p : Pattern) (guard : d5503 p = 1) : d2483 p ≤ (0 : Int) + d2875 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2483, d2875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19380 p hg
    simpa only [d2483, d2875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2483, d2875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2483, d2875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19382 (p : Pattern) (guard : d5503 p = 1) : d2484 p ≤ (0 : Int) + d2876 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2484, d2876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19379 p hg
    simpa only [d2484, d2876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2484, d2876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19381 p hg
    simpa only [d2484, d2876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19383 (p : Pattern) (guard : d5503 p = 1) : d2485 p ≤ (0 : Int) + d2877 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2485, d2877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19377 p hg
    simpa only [d2485, d2877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2485, d2877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19382 p hg
    simpa only [d2485, d2877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19384 (p : Pattern) (guard : d5503 p = 1) : d2486 p ≤ (0 : Int) + d2878 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2486, d2878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19373 p hg
    simpa only [d2486, d2878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2486, d2878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19383 p hg
    simpa only [d2486, d2878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19385 (p : Pattern) (guard : d5503 p = 1) : d2487 p ≤ (0 : Int) + d2879 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2487, d2879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19250 p hg
    simpa only [d2487, d2879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2487, d2879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19088 p hg
    simpa only [d2487, d2879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19386 (p : Pattern) (guard : d5503 p = 1) : d2488 p ≤ (0 : Int) + d2880 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2488, d2880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19243 p hg
    simpa only [d2488, d2880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2488, d2880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19385 p hg
    simpa only [d2488, d2880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19387 (p : Pattern) (guard : d5503 p = 1) : d2489 p ≤ (0 : Int) + d2881 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2489, d2881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19245 p hg
    simpa only [d2489, d2881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2489, d2881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19088 p hg
    simpa only [d2489, d2881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19388 (p : Pattern) (guard : d5503 p = 1) : d2490 p ≤ (0 : Int) + d2882 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2490, d2882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19387 p hg
    simpa only [d2490, d2882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2490, d2882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2490, d2882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19389 (p : Pattern) (guard : d5503 p = 1) : d2491 p ≤ (0 : Int) + d2883 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2491, d2883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19386 p hg
    simpa only [d2491, d2883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2491, d2883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19388 p hg
    simpa only [d2491, d2883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19390 (p : Pattern) (guard : d5503 p = 1) : d2492 p ≤ (0 : Int) + d2884 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2492, d2884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19254 p hg
    simpa only [d2492, d2884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2492, d2884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19065 p hg
    simpa only [d2492, d2884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19391 (p : Pattern) (guard : d5503 p = 1) : d2493 p ≤ (0 : Int) + d2885 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2493, d2885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19390 p hg
    simpa only [d2493, d2885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2493, d2885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2493, d2885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19392 (p : Pattern) (guard : d5503 p = 1) : d2494 p ≤ (0 : Int) + d2886 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2494, d2886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19391 p hg
    simpa only [d2494, d2886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2494, d2886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2494, d2886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19393 (p : Pattern) (guard : d5503 p = 1) : d2495 p ≤ (0 : Int) + d2887 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2495, d2887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19389 p hg
    simpa only [d2495, d2887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2495, d2887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19392 p hg
    simpa only [d2495, d2887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19394 (p : Pattern) (guard : d5503 p = 1) : d2496 p ≤ (0 : Int) + d2888 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2496, d2888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19393 p hg
    simpa only [d2496, d2888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2496, d2888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19382 p hg
    simpa only [d2496, d2888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19395 (p : Pattern) (guard : d5503 p = 1) : d2497 p ≤ (0 : Int) + d2889 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2497, d2889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19394 p hg
    simpa only [d2497, d2889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2497, d2889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2497, d2889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19396 (p : Pattern) (guard : d5503 p = 1) : d2498 p ≤ (0 : Int) + d2890 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2498, d2890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19384 p hg
    simpa only [d2498, d2890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2498, d2890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19395 p hg
    simpa only [d2498, d2890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19397 (p : Pattern) (guard : d5503 p = 1) : d2499 p ≤ (0 : Int) + d2891 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2499, d2891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19354 p hg
    simpa only [d2499, d2891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2499, d2891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19396 p hg
    simpa only [d2499, d2891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19398 (p : Pattern) (guard : d5503 p = 1) : d2500 p ≤ (0 : Int) + d2892 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2500, d2892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19141 p hg
    simpa only [d2500, d2892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2500, d2892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19397 p hg
    simpa only [d2500, d2892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19399 (p : Pattern) (guard : d5503 p = 1) : d2501 p ≤ (0 : Int) + d2893 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2501, d2893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19335 p hg
    simpa only [d2501, d2893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2501, d2893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19398 p hg
    simpa only [d2501, d2893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19400 (p : Pattern) (guard : d5503 p = 1) : d2502 p ≤ (0 : Int) + d2894 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2502, d2894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19291 p hg
    simpa only [d2502, d2894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2502, d2894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19399 p hg
    simpa only [d2502, d2894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19401 (p : Pattern) (guard : d5501 p = 1) : d14 p ≤ (0 : Int) + d14 p := by
  omega
theorem compare19402 (p : Pattern) (guard : d5540 p = 1) : d2184 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19401 p hg
    simpa only [d5540, d2184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17976 p hg
    simpa only [d5540, d2184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19403 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1770 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19404 (p : Pattern) (guard : d5540 p = 1) : d2185 p ≤ (0 : Int) + d5541 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2185, d5541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19401 p hg
    simpa only [d5540, d2185, d5541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2185, d5541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19403 p hg
    simpa only [d5540, d2185, d5541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19405 (p : Pattern) (guard : d5540 p = 1) : d2186 p ≤ (0 : Int) + d5542 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2186, d5542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19402 p hg
    simpa only [d2186, d5542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2186, d5542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19404 p hg
    simpa only [d2186, d5542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19406 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1684 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19407 (p : Pattern) (guard : d5540 p = 1) : d2185 p ≤ (0 : Int) + d5543 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2185, d5543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19401 p hg
    simpa only [d5540, d2185, d5543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2185, d5543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19406 p hg
    simpa only [d5540, d2185, d5543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19408 (p : Pattern) (guard : d5540 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare19409 (p : Pattern) (guard : d5540 p = 1) : d2187 p ≤ (0 : Int) + d5544 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2187, d5544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19407 p hg
    simpa only [d2187, d5544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2187, d5544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2187, d5544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19410 (p : Pattern) (guard : d5540 p = 1) : d2188 p ≤ (0 : Int) + d5545 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2188, d5545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19405 p hg
    simpa only [d2188, d5545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2188, d5545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19409 p hg
    simpa only [d2188, d5545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19411 (p : Pattern) (guard : d5540 p = 1) : d2189 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19401 p hg
    simpa only [d5540, d2189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17982 p hg
    simpa only [d5540, d2189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19412 (p : Pattern) (guard : d5540 p = 1) : d2190 p ≤ (0 : Int) + d5542 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2190, d5542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19411 p hg
    simpa only [d2190, d5542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2190, d5542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19404 p hg
    simpa only [d2190, d5542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19413 (p : Pattern) (guard : d5540 p = 1) : d2191 p ≤ (0 : Int) + d5545 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2191, d5545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19412 p hg
    simpa only [d2191, d5545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2191, d5545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19409 p hg
    simpa only [d2191, d5545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19414 (p : Pattern) (guard : d5540 p = 1) : d2192 p ≤ (0 : Int) + d5545 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19410 p hg
    simpa only [d2192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19413 p hg
    simpa only [d2192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19415 (p : Pattern) (guard : d5540 p = 1) : d2193 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19401 p hg
    simpa only [d5540, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17987 p hg
    simpa only [d5540, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19416 (p : Pattern) (guard : d5540 p = 1) : d2194 p ≤ (0 : Int) + d5542 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2194, d5542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19415 p hg
    simpa only [d2194, d5542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2194, d5542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19404 p hg
    simpa only [d2194, d5542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19417 (p : Pattern) (guard : d5540 p = 1) : d2195 p ≤ (0 : Int) + d5545 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2195, d5545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19416 p hg
    simpa only [d2195, d5545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2195, d5545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19409 p hg
    simpa only [d2195, d5545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19418 (p : Pattern) (guard : d5501 p = 1) : d18 p ≤ (0 : Int) + d18 p := by
  omega
theorem compare19419 (p : Pattern) (guard : d5540 p = 1) : d2196 p ≤ (0 : Int) + d18 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19418 p hg
    simpa only [d5540, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5661 p hg
    simpa only [d5540, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19420 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19421 (p : Pattern) (guard : d5540 p = 1) : d2196 p ≤ (0 : Int) + d5546 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2196, d5546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19418 p hg
    simpa only [d5540, d2196, d5546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2196, d5546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19420 p hg
    simpa only [d5540, d2196, d5546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19422 (p : Pattern) (guard : d5540 p = 1) : d2196 p ≤ (0 : Int) + d5547 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d5547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19419 p hg
    simpa only [d5547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d5547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19421 p hg
    simpa only [d5547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19423 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1694 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19424 (p : Pattern) (guard : d5540 p = 1) : d2196 p ≤ (0 : Int) + d5548 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2196, d5548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19418 p hg
    simpa only [d5540, d2196, d5548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2196, d5548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19423 p hg
    simpa only [d5540, d2196, d5548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19425 (p : Pattern) (guard : d5540 p = 1) : d2197 p ≤ (0 : Int) + d5549 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2197, d5549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19424 p hg
    simpa only [d2197, d5549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2197, d5549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2197, d5549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19426 (p : Pattern) (guard : d5540 p = 1) : d2198 p ≤ (0 : Int) + d5550 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2198, d5550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19422 p hg
    simpa only [d2198, d5550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2198, d5550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19425 p hg
    simpa only [d2198, d5550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19427 (p : Pattern) (guard : d5540 p = 1) : d2199 p ≤ (0 : Int) + d5551 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2199, d5551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19417 p hg
    simpa only [d2199, d5551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2199, d5551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19426 p hg
    simpa only [d2199, d5551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19428 (p : Pattern) (guard : d5540 p = 1) : d2200 p ≤ (0 : Int) + d5552 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2200, d5552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19414 p hg
    simpa only [d2200, d5552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2200, d5552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19427 p hg
    simpa only [d2200, d5552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19429 (p : Pattern) (guard : d5540 p = 1) : d2185 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19401 p hg
    simpa only [d5540, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5657 p hg
    simpa only [d5540, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19430 (p : Pattern) (guard : d5540 p = 1) : d2185 p ≤ (0 : Int) + d5542 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d5542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19429 p hg
    simpa only [d5542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d5542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19404 p hg
    simpa only [d5542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19431 (p : Pattern) (guard : d5540 p = 1) : d2201 p ≤ (0 : Int) + d5545 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2201, d5545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19430 p hg
    simpa only [d2201, d5545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2201, d5545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19409 p hg
    simpa only [d2201, d5545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19432 (p : Pattern) (guard : d5540 p = 1) : d2202 p ≤ (0 : Int) + d5551 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2202, d5551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19431 p hg
    simpa only [d2202, d5551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2202, d5551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19426 p hg
    simpa only [d2202, d5551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19433 (p : Pattern) (guard : d5501 p = 1) : d24 p ≤ (0 : Int) + d24 p := by
  omega
theorem compare19434 (p : Pattern) (guard : d5540 p = 1) : d2203 p ≤ (0 : Int) + d24 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19433 p hg
    simpa only [d5540, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5667 p hg
    simpa only [d5540, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19435 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d356 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19436 (p : Pattern) (guard : d5540 p = 1) : d2203 p ≤ (0 : Int) + d5553 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2203, d5553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19433 p hg
    simpa only [d5540, d2203, d5553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2203, d5553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19435 p hg
    simpa only [d5540, d2203, d5553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19437 (p : Pattern) (guard : d5540 p = 1) : d2203 p ≤ (0 : Int) + d5554 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d5554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19434 p hg
    simpa only [d5554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d5554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19436 p hg
    simpa only [d5554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19438 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1702 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19439 (p : Pattern) (guard : d5540 p = 1) : d2203 p ≤ (0 : Int) + d5555 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2203, d5555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19433 p hg
    simpa only [d5540, d2203, d5555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2203, d5555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19438 p hg
    simpa only [d5540, d2203, d5555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19440 (p : Pattern) (guard : d5540 p = 1) : d2204 p ≤ (0 : Int) + d5556 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2204, d5556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19439 p hg
    simpa only [d2204, d5556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2204, d5556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2204, d5556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19441 (p : Pattern) (guard : d5540 p = 1) : d2205 p ≤ (0 : Int) + d5557 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2205, d5557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19437 p hg
    simpa only [d2205, d5557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2205, d5557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19440 p hg
    simpa only [d2205, d5557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19442 (p : Pattern) (guard : d5540 p = 1) : d2206 p ≤ (0 : Int) + d5558 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2206, d5558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19441 p hg
    simpa only [d2206, d5558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2206, d5558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2206, d5558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19443 (p : Pattern) (guard : d5540 p = 1) : d2207 p ≤ (0 : Int) + d5559 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2207, d5559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19432 p hg
    simpa only [d2207, d5559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2207, d5559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19442 p hg
    simpa only [d2207, d5559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19444 (p : Pattern) (guard : d5540 p = 1) : d2208 p ≤ (0 : Int) + d5560 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2208, d5560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19428 p hg
    simpa only [d2208, d5560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2208, d5560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19443 p hg
    simpa only [d2208, d5560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19445 (p : Pattern) (guard : d5501 p = 1) : d31 p ≤ (0 : Int) + d31 p := by
  omega
theorem compare19446 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1714 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19447 (p : Pattern) (guard : d5540 p = 1) : d2209 p ≤ (0 : Int) + d5561 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2209, d5561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19445 p hg
    simpa only [d5540, d2209, d5561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2209, d5561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19446 p hg
    simpa only [d5540, d2209, d5561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19448 (p : Pattern) (guard : d5540 p = 1) : d2210 p ≤ (0 : Int) + d5562 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2210, d5562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19447 p hg
    simpa only [d2210, d5562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2210, d5562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2210, d5562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19449 (p : Pattern) (guard : d5540 p = 1) : d2211 p ≤ (0 : Int) + d5563 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2211, d5563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19430 p hg
    simpa only [d2211, d5563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2211, d5563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19448 p hg
    simpa only [d2211, d5563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19450 (p : Pattern) (guard : d5501 p = 1) : d35 p ≤ (0 : Int) + d35 p := by
  omega
theorem compare19451 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1722 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19452 (p : Pattern) (guard : d5540 p = 1) : d2212 p ≤ (0 : Int) + d5564 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2212, d5564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19450 p hg
    simpa only [d5540, d2212, d5564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2212, d5564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19451 p hg
    simpa only [d5540, d2212, d5564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19453 (p : Pattern) (guard : d5540 p = 1) : d2213 p ≤ (0 : Int) + d5565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2213, d5565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19452 p hg
    simpa only [d2213, d5565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2213, d5565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2213, d5565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19454 (p : Pattern) (guard : d5540 p = 1) : d2214 p ≤ (0 : Int) + d5566 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2214, d5566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19430 p hg
    simpa only [d2214, d5566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2214, d5566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19453 p hg
    simpa only [d2214, d5566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19455 (p : Pattern) (guard : d5540 p = 1) : d2215 p ≤ (0 : Int) + d5567 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2215, d5567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19449 p hg
    simpa only [d2215, d5567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2215, d5567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19454 p hg
    simpa only [d2215, d5567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19456 (p : Pattern) (guard : d5501 p = 1) : d40 p ≤ (0 : Int) + d40 p := by
  omega
theorem compare19457 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d327 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare19458 (p : Pattern) (guard : d5540 p = 1) : d2216 p ≤ (0 : Int) + d5568 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d2216, d5568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19456 p hg
    simpa only [d5540, d2216, d5568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d2216, d5568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19457 p hg
    simpa only [d5540, d2216, d5568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19459 (p : Pattern) (guard : d5540 p = 1) : d2217 p ≤ (0 : Int) + d5569 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2217, d5569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19458 p hg
    simpa only [d2217, d5569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2217, d5569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d2217, d5569, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
