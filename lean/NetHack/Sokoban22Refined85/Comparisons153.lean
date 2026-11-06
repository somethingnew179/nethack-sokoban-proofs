/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons152
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare21420 (p : Pattern) (guard : d5502 p = 1) : d2748 p ≤ (0 : Int) + d3043 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2748, d3043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21363 p hg
    simpa only [d2748, d3043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2748, d3043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21419 p hg
    simpa only [d2748, d3043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21421 (p : Pattern) (guard : d5502 p = 1) : d2749 p ≤ (0 : Int) + d3044 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2749, d3044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21418 p hg
    simpa only [d2749, d3044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2749, d3044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21420 p hg
    simpa only [d2749, d3044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21422 (p : Pattern) (guard : d5502 p = 1) : d2750 p ≤ (0 : Int) + d3045 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2750, d3045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21416 p hg
    simpa only [d2750, d3045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2750, d3045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21421 p hg
    simpa only [d2750, d3045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21423 (p : Pattern) (guard : d5502 p = 1) : d2751 p ≤ (0 : Int) + d3046 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2751, d3046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21421 p hg
    simpa only [d2751, d3046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2751, d3046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21338 p hg
    simpa only [d2751, d3046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21424 (p : Pattern) (guard : d5502 p = 1) : d2752 p ≤ (0 : Int) + d3047 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2752, d3047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21422 p hg
    simpa only [d2752, d3047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2752, d3047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21423 p hg
    simpa only [d2752, d3047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21425 (p : Pattern) (guard : d5502 p = 1) : d2753 p ≤ (0 : Int) + d3048 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2753, d3048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21392 p hg
    simpa only [d2753, d3048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2753, d3048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21350 p hg
    simpa only [d2753, d3048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21426 (p : Pattern) (guard : d5502 p = 1) : d2707 p ≤ (0 : Int) + d120 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3159 p hg
    simpa only [d5502, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5854 p hg
    simpa only [d5502, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21427 (p : Pattern) (guard : d5502 p = 1) : d2754 p ≤ (0 : Int) + d3049 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2754, d3049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21426 p hg
    simpa only [d2754, d3049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2754, d3049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21354 p hg
    simpa only [d2754, d3049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21428 (p : Pattern) (guard : d5502 p = 1) : d2755 p ≤ (0 : Int) + d3050 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2755, d3050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21427 p hg
    simpa only [d2755, d3050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2755, d3050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21355 p hg
    simpa only [d2755, d3050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21429 (p : Pattern) (guard : d5502 p = 1) : d2756 p ≤ (0 : Int) + d3051 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2756, d3051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21425 p hg
    simpa only [d2756, d3051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2756, d3051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21428 p hg
    simpa only [d2756, d3051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21430 (p : Pattern) (guard : d5502 p = 1) : d2757 p ≤ (0 : Int) + d3052 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2757, d3052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21429 p hg
    simpa only [d2757, d3052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2757, d3052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2757, d3052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21431 (p : Pattern) (guard : d5502 p = 1) : d2758 p ≤ (0 : Int) + d3053 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2758, d3053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21430 p hg
    simpa only [d2758, d3053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2758, d3053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2758, d3053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21432 (p : Pattern) (guard : d5502 p = 1) : d2759 p ≤ (0 : Int) + d3054 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2759, d3054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21424 p hg
    simpa only [d2759, d3054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2759, d3054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21431 p hg
    simpa only [d2759, d3054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21433 (p : Pattern) (guard : d5502 p = 1) : d2760 p ≤ (0 : Int) + d3055 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2760, d3055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21415 p hg
    simpa only [d2760, d3055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2760, d3055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21425 p hg
    simpa only [d2760, d3055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21434 (p : Pattern) (guard : d5502 p = 1) : d2761 p ≤ (0 : Int) + d3056 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2761, d3056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21420 p hg
    simpa only [d2761, d3056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2761, d3056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21196 p hg
    simpa only [d2761, d3056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21435 (p : Pattern) (guard : d5502 p = 1) : d2762 p ≤ (0 : Int) + d3057 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2762, d3057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21433 p hg
    simpa only [d2762, d3057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2762, d3057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21434 p hg
    simpa only [d2762, d3057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21436 (p : Pattern) (guard : d5502 p = 1) : d2763 p ≤ (0 : Int) + d3058 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2763, d3058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21420 p hg
    simpa only [d2763, d3058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2763, d3058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21200 p hg
    simpa only [d2763, d3058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21437 (p : Pattern) (guard : d5502 p = 1) : d2764 p ≤ (0 : Int) + d3059 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2764, d3059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21436 p hg
    simpa only [d2764, d3059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2764, d3059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2764, d3059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21438 (p : Pattern) (guard : d5502 p = 1) : d2765 p ≤ (0 : Int) + d3060 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2765, d3060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21435 p hg
    simpa only [d2765, d3060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2765, d3060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21437 p hg
    simpa only [d2765, d3060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21439 (p : Pattern) (guard : d5502 p = 1) : d2766 p ≤ (0 : Int) + d3061 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2766, d3061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21428 p hg
    simpa only [d2766, d3061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2766, d3061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2766, d3061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21440 (p : Pattern) (guard : d5502 p = 1) : d2767 p ≤ (0 : Int) + d3062 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2767, d3062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21439 p hg
    simpa only [d2767, d3062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2767, d3062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2767, d3062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21441 (p : Pattern) (guard : d5502 p = 1) : d2768 p ≤ (0 : Int) + d3063 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2768, d3063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21440 p hg
    simpa only [d2768, d3063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2768, d3063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2768, d3063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21442 (p : Pattern) (guard : d5502 p = 1) : d2769 p ≤ (0 : Int) + d3064 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2769, d3064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21438 p hg
    simpa only [d2769, d3064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2769, d3064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21441 p hg
    simpa only [d2769, d3064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21443 (p : Pattern) (guard : d5502 p = 1) : d2770 p ≤ (0 : Int) + d3065 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2770, d3065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21432 p hg
    simpa only [d2770, d3065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2770, d3065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21442 p hg
    simpa only [d2770, d3065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21444 (p : Pattern) (guard : d5502 p = 1) : d2771 p ≤ (0 : Int) + d3066 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2771, d3066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21401 p hg
    simpa only [d2771, d3066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2771, d3066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21443 p hg
    simpa only [d2771, d3066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21445 (p : Pattern) (guard : d5502 p = 1) : d2772 p ≤ (0 : Int) + d3067 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2772, d3067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21338 p hg
    simpa only [d2772, d3067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2772, d3067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2772, d3067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21446 (p : Pattern) (guard : d5502 p = 1) : d2773 p ≤ (0 : Int) + d3068 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2773, d3068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21445 p hg
    simpa only [d2773, d3068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2773, d3068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2773, d3068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21447 (p : Pattern) (guard : d5502 p = 1) : d2774 p ≤ (0 : Int) + d3069 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2774, d3069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21446 p hg
    simpa only [d2774, d3069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2774, d3069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2774, d3069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21448 (p : Pattern) (guard : d5502 p = 1) : d2775 p ≤ (0 : Int) + d3070 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2775, d3070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21447 p hg
    simpa only [d2775, d3070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2775, d3070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2775, d3070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21449 (p : Pattern) (guard : d5502 p = 1) : d2776 p ≤ (0 : Int) + d3071 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2776, d3071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21443 p hg
    simpa only [d2776, d3071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2776, d3071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21448 p hg
    simpa only [d2776, d3071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21450 (p : Pattern) (guard : d5502 p = 1) : d2777 p ≤ (0 : Int) + d3072 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2777, d3072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21444 p hg
    simpa only [d2777, d3072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2777, d3072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21449 p hg
    simpa only [d2777, d3072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21451 (p : Pattern) (guard : d5502 p = 1) : d2778 p ≤ (0 : Int) + d2998 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2778, d2998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21324 p hg
    simpa only [d2778, d2998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2778, d2998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21336 p hg
    simpa only [d2778, d2998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21452 (p : Pattern) (guard : d5502 p = 1) : d2779 p ≤ (0 : Int) + d3001 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2779, d3001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21451 p hg
    simpa only [d2779, d3001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2779, d3001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21339 p hg
    simpa only [d2779, d3001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21453 (p : Pattern) (guard : d5502 p = 1) : d2780 p ≤ (0 : Int) + d3014 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2780, d3014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21452 p hg
    simpa only [d2780, d3014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2780, d3014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21369 p hg
    simpa only [d2780, d3014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21454 (p : Pattern) (guard : d5502 p = 1) : d2781 p ≤ (0 : Int) + d3017 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2781, d3017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21324 p hg
    simpa only [d2781, d3017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2781, d3017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21385 p hg
    simpa only [d2781, d3017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21455 (p : Pattern) (guard : d5502 p = 1) : d2782 p ≤ (0 : Int) + d3019 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2782, d3019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21454 p hg
    simpa only [d2782, d3019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2782, d3019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21387 p hg
    simpa only [d2782, d3019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21456 (p : Pattern) (guard : d5502 p = 1) : d2783 p ≤ (0 : Int) + d3022 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2783, d3022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21455 p hg
    simpa only [d2783, d3022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2783, d3022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21390 p hg
    simpa only [d2783, d3022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21457 (p : Pattern) (guard : d5502 p = 1) : d2784 p ≤ (0 : Int) + d3031 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2784, d3031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21456 p hg
    simpa only [d2784, d3031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2784, d3031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21399 p hg
    simpa only [d2784, d3031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21458 (p : Pattern) (guard : d5502 p = 1) : d2785 p ≤ (0 : Int) + d3032 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2785, d3032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21453 p hg
    simpa only [d2785, d3032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2785, d3032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21457 p hg
    simpa only [d2785, d3032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21459 (p : Pattern) (guard : d5502 p = 1) : d2786 p ≤ (0 : Int) + d3066 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2786, d3066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21458 p hg
    simpa only [d2786, d3066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2786, d3066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21443 p hg
    simpa only [d2786, d3066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21460 (p : Pattern) (guard : d5502 p = 1) : d2787 p ≤ (0 : Int) + d3073 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2787, d3073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21443 p hg
    simpa only [d2787, d3073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2787, d3073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2787, d3073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21461 (p : Pattern) (guard : d5502 p = 1) : d2788 p ≤ (0 : Int) + d3074 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2788, d3074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21459 p hg
    simpa only [d2788, d3074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2788, d3074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21460 p hg
    simpa only [d2788, d3074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21462 (p : Pattern) (guard : d5502 p = 1) : d2789 p ≤ (0 : Int) + d3075 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2789, d3075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21450 p hg
    simpa only [d2789, d3075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2789, d3075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21461 p hg
    simpa only [d2789, d3075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21463 (p : Pattern) (guard : d5502 p = 1) : d2790 p ≤ (0 : Int) + d3076 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2790, d3076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21285 p hg
    simpa only [d2790, d3076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2790, d3076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21462 p hg
    simpa only [d2790, d3076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21464 (p : Pattern) (guard : d5502 p = 1) : d2791 p ≤ (0 : Int) + d3077 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2791, d3077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21309 p hg
    simpa only [d2791, d3077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2791, d3077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21463 p hg
    simpa only [d2791, d3077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21465 (p : Pattern) (guard : d5502 p = 1) : d2521 p ≤ (0 : Int) + d3078 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2521, d3078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17222 p hg
    simpa only [d5502, d2521, d3078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2521, d3078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21157 p hg
    simpa only [d5502, d2521, d3078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21466 (p : Pattern) (guard : d5502 p = 1) : d2522 p ≤ (0 : Int) + d3079 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2522, d3079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21158 p hg
    simpa only [d2522, d3079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2522, d3079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21465 p hg
    simpa only [d2522, d3079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21467 (p : Pattern) (guard : d5502 p = 1) : d2523 p ≤ (0 : Int) + d3080 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2523, d3080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21109 p hg
    simpa only [d2523, d3080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2523, d3080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21466 p hg
    simpa only [d2523, d3080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21468 (p : Pattern) (guard : d5502 p = 1) : d2602 p ≤ (0 : Int) + d2013 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2602, d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21112 p hg
    simpa only [d2602, d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2602, d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2602, d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21469 (p : Pattern) (guard : d5502 p = 1) : d2603 p ≤ (0 : Int) + d3081 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2603, d3081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21467 p hg
    simpa only [d2603, d3081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2603, d3081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21468 p hg
    simpa only [d2603, d3081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21470 (p : Pattern) (guard : d5502 p = 1) : d2604 p ≤ (0 : Int) + d3082 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2604, d3082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21221 p hg
    simpa only [d2604, d3082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2604, d3082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21469 p hg
    simpa only [d2604, d3082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21471 (p : Pattern) (guard : d5502 p = 1) : d2605 p ≤ (0 : Int) + d3083 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2605, d3083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21221 p hg
    simpa only [d2605, d3083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2605, d3083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21470 p hg
    simpa only [d2605, d3083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21472 (p : Pattern) (guard : d5502 p = 1) : d2609 p ≤ (0 : Int) + d3084 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2609, d3084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21470 p hg
    simpa only [d2609, d3084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2609, d3084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21240 p hg
    simpa only [d2609, d3084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21473 (p : Pattern) (guard : d5502 p = 1) : d2610 p ≤ (0 : Int) + d3085 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2610, d3085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21471 p hg
    simpa only [d2610, d3085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2610, d3085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21472 p hg
    simpa only [d2610, d3085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21474 (p : Pattern) (guard : d5502 p = 1) : d2792 p ≤ (0 : Int) + d3086 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2792, d3086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21204 p hg
    simpa only [d2792, d3086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2792, d3086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21149 p hg
    simpa only [d2792, d3086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21475 (p : Pattern) (guard : d5502 p = 1) : d2793 p ≤ (0 : Int) + d3087 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2793, d3087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21243 p hg
    simpa only [d2793, d3087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2793, d3087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21474 p hg
    simpa only [d2793, d3087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21476 (p : Pattern) (guard : d5502 p = 1) : d2794 p ≤ (0 : Int) + d3088 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2794, d3088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21204 p hg
    simpa only [d2794, d3088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2794, d3088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21155 p hg
    simpa only [d2794, d3088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21477 (p : Pattern) (guard : d5502 p = 1) : d2795 p ≤ (0 : Int) + d3089 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2795, d3089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21245 p hg
    simpa only [d2795, d3089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2795, d3089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2795, d3089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21478 (p : Pattern) (guard : d5502 p = 1) : d2796 p ≤ (0 : Int) + d3090 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2796, d3090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21476 p hg
    simpa only [d2796, d3090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2796, d3090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21477 p hg
    simpa only [d2796, d3090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21479 (p : Pattern) (guard : d5502 p = 1) : d2797 p ≤ (0 : Int) + d3091 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2797, d3091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21475 p hg
    simpa only [d2797, d3091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2797, d3091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21478 p hg
    simpa only [d2797, d3091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21480 (p : Pattern) (guard : d5502 p = 1) : d2798 p ≤ (0 : Int) + d3092 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2798, d3092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21205 p hg
    simpa only [d2798, d3092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2798, d3092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21477 p hg
    simpa only [d2798, d3092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21481 (p : Pattern) (guard : d5502 p = 1) : d2799 p ≤ (0 : Int) + d3093 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2799, d3093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21480 p hg
    simpa only [d2799, d3093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2799, d3093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21212 p hg
    simpa only [d2799, d3093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21482 (p : Pattern) (guard : d5502 p = 1) : d2800 p ≤ (0 : Int) + d3094 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2800, d3094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21479 p hg
    simpa only [d2800, d3094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2800, d3094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21481 p hg
    simpa only [d2800, d3094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21483 (p : Pattern) (guard : d5502 p = 1) : d2801 p ≤ (0 : Int) + d3095 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2801, d3095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21473 p hg
    simpa only [d2801, d3095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2801, d3095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21482 p hg
    simpa only [d2801, d3095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21484 (p : Pattern) (guard : d5502 p = 1) : d2541 p ≤ (0 : Int) + d3096 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2541, d3096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17125 p hg
    simpa only [d5502, d2541, d3096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2541, d3096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21140 p hg
    simpa only [d5502, d2541, d3096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21485 (p : Pattern) (guard : d5502 p = 1) : d2542 p ≤ (0 : Int) + d3097 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2542, d3097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21141 p hg
    simpa only [d2542, d3097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2542, d3097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21484 p hg
    simpa only [d2542, d3097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21486 (p : Pattern) (guard : d5502 p = 1) : d2569 p ≤ (0 : Int) + d3098 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2569, d3098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21177 p hg
    simpa only [d2569, d3098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2569, d3098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21485 p hg
    simpa only [d2569, d3098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21487 (p : Pattern) (guard : d5502 p = 1) : d2543 p ≤ (0 : Int) + d2031 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2543, d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21180 p hg
    simpa only [d2543, d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2543, d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2543, d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21488 (p : Pattern) (guard : d5502 p = 1) : d2611 p ≤ (0 : Int) + d3099 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2611, d3099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21486 p hg
    simpa only [d2611, d3099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2611, d3099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21487 p hg
    simpa only [d2611, d3099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21489 (p : Pattern) (guard : d5502 p = 1) : d2618 p ≤ (0 : Int) + d3100 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2618, d3100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21221 p hg
    simpa only [d2618, d3100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2618, d3100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21488 p hg
    simpa only [d2618, d3100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21490 (p : Pattern) (guard : d5502 p = 1) : d2619 p ≤ (0 : Int) + d3101 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2619, d3101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21469 p hg
    simpa only [d2619, d3101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2619, d3101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21239 p hg
    simpa only [d2619, d3101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21491 (p : Pattern) (guard : d5502 p = 1) : d2620 p ≤ (0 : Int) + d3102 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2620, d3102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21489 p hg
    simpa only [d2620, d3102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2620, d3102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21490 p hg
    simpa only [d2620, d3102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21492 (p : Pattern) (guard : d5502 p = 1) : d2621 p ≤ (0 : Int) + d3103 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2621, d3103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21469 p hg
    simpa only [d2621, d3103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2621, d3103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21196 p hg
    simpa only [d2621, d3103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21493 (p : Pattern) (guard : d5502 p = 1) : d2622 p ≤ (0 : Int) + d3104 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2622, d3104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21492 p hg
    simpa only [d2622, d3104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2622, d3104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21201 p hg
    simpa only [d2622, d3104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21494 (p : Pattern) (guard : d5502 p = 1) : d2623 p ≤ (0 : Int) + d3105 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2623, d3105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21491 p hg
    simpa only [d2623, d3105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2623, d3105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21493 p hg
    simpa only [d2623, d3105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21495 (p : Pattern) (guard : d5502 p = 1) : d2802 p ≤ (0 : Int) + d3106 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2802, d3106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21474 p hg
    simpa only [d2802, d3106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2802, d3106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21162 p hg
    simpa only [d2802, d3106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21496 (p : Pattern) (guard : d5502 p = 1) : d2803 p ≤ (0 : Int) + d3107 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2803, d3107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21477 p hg
    simpa only [d2803, d3107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2803, d3107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21211 p hg
    simpa only [d2803, d3107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21497 (p : Pattern) (guard : d5502 p = 1) : d2804 p ≤ (0 : Int) + d3108 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2804, d3108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21495 p hg
    simpa only [d2804, d3108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2804, d3108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21496 p hg
    simpa only [d2804, d3108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21498 (p : Pattern) (guard : d5502 p = 1) : d2805 p ≤ (0 : Int) + d3109 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2805, d3109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21477 p hg
    simpa only [d2805, d3109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2805, d3109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2805, d3109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21499 (p : Pattern) (guard : d5502 p = 1) : d2806 p ≤ (0 : Int) + d3110 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2806, d3110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21498 p hg
    simpa only [d2806, d3110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2806, d3110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2806, d3110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21500 (p : Pattern) (guard : d5502 p = 1) : d2807 p ≤ (0 : Int) + d3111 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2807, d3111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21497 p hg
    simpa only [d2807, d3111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2807, d3111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21499 p hg
    simpa only [d2807, d3111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21501 (p : Pattern) (guard : d5502 p = 1) : d2808 p ≤ (0 : Int) + d3112 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2808, d3112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21494 p hg
    simpa only [d2808, d3112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2808, d3112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21500 p hg
    simpa only [d2808, d3112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21502 (p : Pattern) (guard : d5502 p = 1) : d2809 p ≤ (0 : Int) + d3113 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2809, d3113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21483 p hg
    simpa only [d2809, d3113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2809, d3113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21501 p hg
    simpa only [d2809, d3113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21503 (p : Pattern) (guard : d5502 p = 1) : d2518 p ≤ (0 : Int) + d3114 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2518, d3114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21089 p hg
    simpa only [d2518, d3114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2518, d3114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21228 p hg
    simpa only [d2518, d3114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21504 (p : Pattern) (guard : d5502 p = 1) : d2600 p ≤ (0 : Int) + d2049 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2600, d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21218 p hg
    simpa only [d2600, d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2600, d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2600, d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21505 (p : Pattern) (guard : d5502 p = 1) : d2601 p ≤ (0 : Int) + d3115 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2601, d3115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21503 p hg
    simpa only [d2601, d3115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2601, d3115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21504 p hg
    simpa only [d2601, d3115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21506 (p : Pattern) (guard : d5502 p = 1) : d2600 p ≤ (0 : Int) + d2055 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2600, d2055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21224 p hg
    simpa only [d2600, d2055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2600, d2055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2600, d2055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21507 (p : Pattern) (guard : d5502 p = 1) : d2601 p ≤ (0 : Int) + d3116 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2601, d3116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21139 p hg
    simpa only [d2601, d3116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2601, d3116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21506 p hg
    simpa only [d2601, d3116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21508 (p : Pattern) (guard : d5502 p = 1) : d2601 p ≤ (0 : Int) + d3117 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21505 p hg
    simpa only [d3117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21507 p hg
    simpa only [d3117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21509 (p : Pattern) (guard : d5502 p = 1) : d2810 p ≤ (0 : Int) + d3118 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2810, d3118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21508 p hg
    simpa only [d2810, d3118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2810, d3118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21247 p hg
    simpa only [d2810, d3118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21510 (p : Pattern) (guard : d5502 p = 1) : d2811 p ≤ (0 : Int) + d3119 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2811, d3119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21509 p hg
    simpa only [d2811, d3119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2811, d3119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21248 p hg
    simpa only [d2811, d3119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21511 (p : Pattern) (guard : d5502 p = 1) : d2812 p ≤ (0 : Int) + d191 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5250 p hg
    simpa only [d5502, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15557 p hg
    simpa only [d5502, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21512 (p : Pattern) (guard : d5502 p = 1) : d2812 p ≤ (0 : Int) + d2060 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2812, d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5250 p hg
    simpa only [d5502, d2812, d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2812, d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19737 p hg
    simpa only [d5502, d2812, d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21513 (p : Pattern) (guard : d5502 p = 1) : d320 p ≤ (0 : Int) + d315 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17514 p hg
    simpa only [d5502, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19737 p hg
    simpa only [d5502, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21514 (p : Pattern) (guard : d5502 p = 1) : d2813 p ≤ (0 : Int) + d2061 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2813, d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21512 p hg
    simpa only [d2813, d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2813, d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21513 p hg
    simpa only [d2813, d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21515 (p : Pattern) (guard : d5502 p = 1) : d2814 p ≤ (0 : Int) + d3120 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2814, d3120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21511 p hg
    simpa only [d2814, d3120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2814, d3120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21514 p hg
    simpa only [d2814, d3120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21516 (p : Pattern) (guard : d5502 p = 1) : d2815 p ≤ (0 : Int) + d2062 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2815, d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21514 p hg
    simpa only [d2815, d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2815, d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2815, d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21517 (p : Pattern) (guard : d5502 p = 1) : d2816 p ≤ (0 : Int) + d3121 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2816, d3121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21515 p hg
    simpa only [d2816, d3121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2816, d3121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21516 p hg
    simpa only [d2816, d3121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21518 (p : Pattern) (guard : d5502 p = 1) : d2817 p ≤ (0 : Int) + d3122 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2817, d3122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21235 p hg
    simpa only [d2817, d3122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2817, d3122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21517 p hg
    simpa only [d2817, d3122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21519 (p : Pattern) (guard : d5502 p = 1) : d2818 p ≤ (0 : Int) + d3123 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2818, d3123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21518 p hg
    simpa only [d2818, d3123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2818, d3123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2818, d3123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21520 (p : Pattern) (guard : d5502 p = 1) : d2819 p ≤ (0 : Int) + d3124 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2819, d3124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21519 p hg
    simpa only [d2819, d3124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2819, d3124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2819, d3124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21521 (p : Pattern) (guard : d5502 p = 1) : d2820 p ≤ (0 : Int) + d3125 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2820, d3125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21510 p hg
    simpa only [d2820, d3125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2820, d3125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21520 p hg
    simpa only [d2820, d3125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21522 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2069 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21523 (p : Pattern) (guard : d5502 p = 1) : d2541 p ≤ (0 : Int) + d2070 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2541, d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17125 p hg
    simpa only [d5502, d2541, d2070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2541, d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21522 p hg
    simpa only [d5502, d2541, d2070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21524 (p : Pattern) (guard : d5502 p = 1) : d2542 p ≤ (0 : Int) + d2071 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2542, d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21141 p hg
    simpa only [d2542, d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2542, d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21523 p hg
    simpa only [d2542, d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21525 (p : Pattern) (guard : d5502 p = 1) : d2543 p ≤ (0 : Int) + d2072 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2543, d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21524 p hg
    simpa only [d2543, d2072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2543, d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2543, d2072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21526 (p : Pattern) (guard : d5502 p = 1) : d2611 p ≤ (0 : Int) + d3126 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2611, d3126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21204 p hg
    simpa only [d2611, d3126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2611, d3126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21525 p hg
    simpa only [d2611, d3126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21527 (p : Pattern) (guard : d5502 p = 1) : d2611 p ≤ (0 : Int) + d3127 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21526 p hg
    simpa only [d3127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21243 p hg
    simpa only [d3127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21528 (p : Pattern) (guard : d5502 p = 1) : d2821 p ≤ (0 : Int) + d3128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2821, d3128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21235 p hg
    simpa only [d2821, d3128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2821, d3128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21200 p hg
    simpa only [d2821, d3128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21529 (p : Pattern) (guard : d5502 p = 1) : d2822 p ≤ (0 : Int) + d3129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2822, d3129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21527 p hg
    simpa only [d2822, d3129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2822, d3129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21528 p hg
    simpa only [d2822, d3129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21530 (p : Pattern) (guard : d5502 p = 1) : d2823 p ≤ (0 : Int) + d3130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2823, d3130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21529 p hg
    simpa only [d2823, d3130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2823, d3130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21258 p hg
    simpa only [d2823, d3130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21531 (p : Pattern) (guard : d5502 p = 1) : d2824 p ≤ (0 : Int) + d3131 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2824, d3131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21517 p hg
    simpa only [d2824, d3131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2824, d3131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2824, d3131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21532 (p : Pattern) (guard : d5502 p = 1) : d2825 p ≤ (0 : Int) + d3132 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2825, d3132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21531 p hg
    simpa only [d2825, d3132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2825, d3132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2825, d3132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21533 (p : Pattern) (guard : d5502 p = 1) : d2826 p ≤ (0 : Int) + d3133 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2826, d3133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21532 p hg
    simpa only [d2826, d3133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2826, d3133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2826, d3133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21534 (p : Pattern) (guard : d5502 p = 1) : d2827 p ≤ (0 : Int) + d3134 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2827, d3134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21530 p hg
    simpa only [d2827, d3134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2827, d3134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21533 p hg
    simpa only [d2827, d3134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21535 (p : Pattern) (guard : d5502 p = 1) : d2828 p ≤ (0 : Int) + d3135 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2828, d3135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21521 p hg
    simpa only [d2828, d3135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2828, d3135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21534 p hg
    simpa only [d2828, d3135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21536 (p : Pattern) (guard : d5502 p = 1) : d2829 p ≤ (0 : Int) + d3136 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2829, d3136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21502 p hg
    simpa only [d2829, d3136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2829, d3136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21535 p hg
    simpa only [d2829, d3136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21537 (p : Pattern) (guard : d5502 p = 1) : d2830 p ≤ (0 : Int) + d3137 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2830, d3137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21535 p hg
    simpa only [d2830, d3137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2830, d3137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2830, d3137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21538 (p : Pattern) (guard : d5502 p = 1) : d2831 p ≤ (0 : Int) + d3138 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2831, d3138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21536 p hg
    simpa only [d2831, d3138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2831, d3138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21537 p hg
    simpa only [d2831, d3138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21539 (p : Pattern) (guard : d5502 p = 1) : d2832 p ≤ (0 : Int) + d3139 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2832, d3139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21301 p hg
    simpa only [d2832, d3139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2832, d3139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21538 p hg
    simpa only [d2832, d3139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21540 (p : Pattern) (guard : d5502 p = 1) : d2833 p ≤ (0 : Int) + d3140 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2833, d3140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21285 p hg
    simpa only [d2833, d3140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2833, d3140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21539 p hg
    simpa only [d2833, d3140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21541 (p : Pattern) (guard : d5502 p = 1) : d2834 p ≤ (0 : Int) + d3141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2834, d3141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21335 p hg
    simpa only [d2834, d3141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2834, d3141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2834, d3141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21542 (p : Pattern) (guard : d5502 p = 1) : d2835 p ≤ (0 : Int) + d3142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2835, d3142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21386 p hg
    simpa only [d2835, d3142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2835, d3142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21541 p hg
    simpa only [d2835, d3142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21543 (p : Pattern) (guard : d5502 p = 1) : d2836 p ≤ (0 : Int) + d3143 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2836, d3143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21541 p hg
    simpa only [d2836, d3143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2836, d3143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2836, d3143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21544 (p : Pattern) (guard : d5502 p = 1) : d2837 p ≤ (0 : Int) + d3144 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2837, d3144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21542 p hg
    simpa only [d2837, d3144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2837, d3144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21543 p hg
    simpa only [d2837, d3144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21545 (p : Pattern) (guard : d5502 p = 1) : d2838 p ≤ (0 : Int) + d3145 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2838, d3145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21364 p hg
    simpa only [d2838, d3145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2838, d3145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2838, d3145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21546 (p : Pattern) (guard : d5502 p = 1) : d2839 p ≤ (0 : Int) + d3146 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2839, d3146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21394 p hg
    simpa only [d2839, d3146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2839, d3146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21545 p hg
    simpa only [d2839, d3146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21547 (p : Pattern) (guard : d5502 p = 1) : d2840 p ≤ (0 : Int) + d3147 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2840, d3147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21545 p hg
    simpa only [d2840, d3147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2840, d3147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2840, d3147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21548 (p : Pattern) (guard : d5502 p = 1) : d2841 p ≤ (0 : Int) + d3148 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2841, d3148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21546 p hg
    simpa only [d2841, d3148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2841, d3148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21547 p hg
    simpa only [d2841, d3148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21549 (p : Pattern) (guard : d5502 p = 1) : d2842 p ≤ (0 : Int) + d3149 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2842, d3149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21544 p hg
    simpa only [d2842, d3149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2842, d3149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21548 p hg
    simpa only [d2842, d3149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21550 (p : Pattern) (guard : d5502 p = 1) : d2843 p ≤ (0 : Int) + d3150 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2843, d3150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21370 p hg
    simpa only [d2843, d3150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2843, d3150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21549 p hg
    simpa only [d2843, d3150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21551 (p : Pattern) (guard : d5502 p = 1) : d2844 p ≤ (0 : Int) + d3151 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2844, d3151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21420 p hg
    simpa only [d2844, d3151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2844, d3151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2844, d3151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21552 (p : Pattern) (guard : d5502 p = 1) : d2845 p ≤ (0 : Int) + d3152 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2845, d3152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21433 p hg
    simpa only [d2845, d3152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2845, d3152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21551 p hg
    simpa only [d2845, d3152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21553 (p : Pattern) (guard : d5502 p = 1) : d2846 p ≤ (0 : Int) + d3153 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2846, d3153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21551 p hg
    simpa only [d2846, d3153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2846, d3153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2846, d3153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21554 (p : Pattern) (guard : d5502 p = 1) : d2847 p ≤ (0 : Int) + d3154 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2847, d3154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21552 p hg
    simpa only [d2847, d3154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2847, d3154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21553 p hg
    simpa only [d2847, d3154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21555 (p : Pattern) (guard : d5502 p = 1) : d2848 p ≤ (0 : Int) + d3155 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2848, d3155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21554 p hg
    simpa only [d2848, d3155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2848, d3155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21441 p hg
    simpa only [d2848, d3155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21556 (p : Pattern) (guard : d5502 p = 1) : d2849 p ≤ (0 : Int) + d3156 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2849, d3156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21432 p hg
    simpa only [d2849, d3156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2849, d3156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21555 p hg
    simpa only [d2849, d3156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21557 (p : Pattern) (guard : d5502 p = 1) : d2850 p ≤ (0 : Int) + d3157 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2850, d3157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21550 p hg
    simpa only [d2850, d3157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2850, d3157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21556 p hg
    simpa only [d2850, d3157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21558 (p : Pattern) (guard : d5502 p = 1) : d2851 p ≤ (0 : Int) + d3158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2851, d3158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21556 p hg
    simpa only [d2851, d3158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2851, d3158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21448 p hg
    simpa only [d2851, d3158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21559 (p : Pattern) (guard : d5502 p = 1) : d2852 p ≤ (0 : Int) + d3159 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2852, d3159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21557 p hg
    simpa only [d2852, d3159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2852, d3159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21558 p hg
    simpa only [d2852, d3159, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
