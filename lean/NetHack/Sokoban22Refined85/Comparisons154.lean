/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons153
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare21560 (p : Pattern) (guard : d5502 p = 1) : d2686 p ≤ (0 : Int) + d3160 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2686, d3160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21312 p hg
    simpa only [d2686, d3160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2686, d3160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21413 p hg
    simpa only [d2686, d3160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21561 (p : Pattern) (guard : d5502 p = 1) : d2745 p ≤ (0 : Int) + d2109 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2745, d2109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21403 p hg
    simpa only [d2745, d2109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2745, d2109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2745, d2109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21562 (p : Pattern) (guard : d5502 p = 1) : d2746 p ≤ (0 : Int) + d3161 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2746, d3161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21560 p hg
    simpa only [d2746, d3161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2746, d3161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21561 p hg
    simpa only [d2746, d3161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21563 (p : Pattern) (guard : d5502 p = 1) : d2749 p ≤ (0 : Int) + d3162 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2749, d3162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21562 p hg
    simpa only [d2749, d3162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2749, d3162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21420 p hg
    simpa only [d2749, d3162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21564 (p : Pattern) (guard : d5502 p = 1) : d2750 p ≤ (0 : Int) + d3163 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2750, d3163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21406 p hg
    simpa only [d2750, d3163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2750, d3163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21563 p hg
    simpa only [d2750, d3163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21565 (p : Pattern) (guard : d5502 p = 1) : d2749 p ≤ (0 : Int) + d3164 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2749, d3164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21415 p hg
    simpa only [d2749, d3164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2749, d3164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21420 p hg
    simpa only [d2749, d3164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21566 (p : Pattern) (guard : d5502 p = 1) : d2751 p ≤ (0 : Int) + d3165 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2751, d3165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21565 p hg
    simpa only [d2751, d3165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2751, d3165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21338 p hg
    simpa only [d2751, d3165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21567 (p : Pattern) (guard : d5502 p = 1) : d2752 p ≤ (0 : Int) + d3166 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2752, d3166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21564 p hg
    simpa only [d2752, d3166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2752, d3166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21566 p hg
    simpa only [d2752, d3166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21568 (p : Pattern) (guard : d5502 p = 1) : d2853 p ≤ (0 : Int) + d3167 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2853, d3167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21392 p hg
    simpa only [d2853, d3167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2853, d3167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21355 p hg
    simpa only [d2853, d3167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21569 (p : Pattern) (guard : d5502 p = 1) : d2854 p ≤ (0 : Int) + d3168 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2854, d3168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21425 p hg
    simpa only [d2854, d3168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2854, d3168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21568 p hg
    simpa only [d2854, d3168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21570 (p : Pattern) (guard : d5502 p = 1) : d2855 p ≤ (0 : Int) + d3169 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2855, d3169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21569 p hg
    simpa only [d2855, d3169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2855, d3169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21545 p hg
    simpa only [d2855, d3169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21571 (p : Pattern) (guard : d5502 p = 1) : d2856 p ≤ (0 : Int) + d3170 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2856, d3170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21427 p hg
    simpa only [d2856, d3170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2856, d3170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2856, d3170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21572 (p : Pattern) (guard : d5502 p = 1) : d2857 p ≤ (0 : Int) + d3171 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2857, d3171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21571 p hg
    simpa only [d2857, d3171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2857, d3171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2857, d3171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21573 (p : Pattern) (guard : d5502 p = 1) : d2858 p ≤ (0 : Int) + d3172 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2858, d3172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21572 p hg
    simpa only [d2858, d3172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2858, d3172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2858, d3172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21574 (p : Pattern) (guard : d5502 p = 1) : d2859 p ≤ (0 : Int) + d3173 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2859, d3173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21570 p hg
    simpa only [d2859, d3173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2859, d3173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21573 p hg
    simpa only [d2859, d3173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21575 (p : Pattern) (guard : d5502 p = 1) : d2860 p ≤ (0 : Int) + d3174 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2860, d3174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21567 p hg
    simpa only [d2860, d3174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2860, d3174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21574 p hg
    simpa only [d2860, d3174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21576 (p : Pattern) (guard : d5502 p = 1) : d2703 p ≤ (0 : Int) + d3175 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2703, d3175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17336 p hg
    simpa only [d5502, d2703, d3175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2703, d3175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21346 p hg
    simpa only [d5502, d2703, d3175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21577 (p : Pattern) (guard : d5502 p = 1) : d2704 p ≤ (0 : Int) + d3176 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2704, d3176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21347 p hg
    simpa only [d2704, d3176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2704, d3176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21576 p hg
    simpa only [d2704, d3176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21578 (p : Pattern) (guard : d5502 p = 1) : d2725 p ≤ (0 : Int) + d3177 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2725, d3177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21376 p hg
    simpa only [d2725, d3177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2725, d3177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21577 p hg
    simpa only [d2725, d3177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21579 (p : Pattern) (guard : d5502 p = 1) : d2705 p ≤ (0 : Int) + d2126 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2705, d2126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21379 p hg
    simpa only [d2705, d2126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2705, d2126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2705, d2126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21580 (p : Pattern) (guard : d5502 p = 1) : d2753 p ≤ (0 : Int) + d3178 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2753, d3178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21578 p hg
    simpa only [d2753, d3178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2753, d3178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21579 p hg
    simpa only [d2753, d3178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21581 (p : Pattern) (guard : d5502 p = 1) : d2760 p ≤ (0 : Int) + d3179 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2760, d3179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21562 p hg
    simpa only [d2760, d3179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2760, d3179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21580 p hg
    simpa only [d2760, d3179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21582 (p : Pattern) (guard : d5502 p = 1) : d2690 p ≤ (0 : Int) + d2135 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2690, d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17408 p hg
    simpa only [d5502, d2690, d2135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2690, d2135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21359 p hg
    simpa only [d5502, d2690, d2135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21583 (p : Pattern) (guard : d5502 p = 1) : d2691 p ≤ (0 : Int) + d2136 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2691, d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21360 p hg
    simpa only [d2691, d2136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2691, d2136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21582 p hg
    simpa only [d2691, d2136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21584 (p : Pattern) (guard : d5502 p = 1) : d2692 p ≤ (0 : Int) + d3180 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2692, d3180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21326 p hg
    simpa only [d2692, d3180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2692, d3180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21583 p hg
    simpa only [d2692, d3180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21585 (p : Pattern) (guard : d5502 p = 1) : d2747 p ≤ (0 : Int) + d2131 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2747, d2131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21329 p hg
    simpa only [d2747, d2131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2747, d2131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2747, d2131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21586 (p : Pattern) (guard : d5502 p = 1) : d2748 p ≤ (0 : Int) + d3181 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2748, d3181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21584 p hg
    simpa only [d2748, d3181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2748, d3181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21585 p hg
    simpa only [d2748, d3181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21587 (p : Pattern) (guard : d5502 p = 1) : d2844 p ≤ (0 : Int) + d3182 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2844, d3182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21586 p hg
    simpa only [d2844, d3182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2844, d3182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2844, d3182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21588 (p : Pattern) (guard : d5502 p = 1) : d2845 p ≤ (0 : Int) + d3183 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2845, d3183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21581 p hg
    simpa only [d2845, d3183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2845, d3183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21587 p hg
    simpa only [d2845, d3183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21589 (p : Pattern) (guard : d5502 p = 1) : d2747 p ≤ (0 : Int) + d2137 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2747, d2137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21583 p hg
    simpa only [d2747, d2137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2747, d2137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2747, d2137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21590 (p : Pattern) (guard : d5502 p = 1) : d2748 p ≤ (0 : Int) + d3184 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2748, d3184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21363 p hg
    simpa only [d2748, d3184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2748, d3184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21589 p hg
    simpa only [d2748, d3184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21591 (p : Pattern) (guard : d5502 p = 1) : d2844 p ≤ (0 : Int) + d3185 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2844, d3185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21590 p hg
    simpa only [d2844, d3185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2844, d3185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2844, d3185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21592 (p : Pattern) (guard : d5502 p = 1) : d2846 p ≤ (0 : Int) + d3186 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2846, d3186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21591 p hg
    simpa only [d2846, d3186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2846, d3186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2846, d3186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21593 (p : Pattern) (guard : d5502 p = 1) : d2847 p ≤ (0 : Int) + d3187 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2847, d3187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21588 p hg
    simpa only [d2847, d3187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2847, d3187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21592 p hg
    simpa only [d2847, d3187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21594 (p : Pattern) (guard : d5502 p = 1) : d2861 p ≤ (0 : Int) + d3188 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2861, d3188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21363 p hg
    simpa only [d2861, d3188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2861, d3188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21355 p hg
    simpa only [d2861, d3188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21595 (p : Pattern) (guard : d5502 p = 1) : d2862 p ≤ (0 : Int) + d3189 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2862, d3189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21594 p hg
    simpa only [d2862, d3189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2862, d3189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21364 p hg
    simpa only [d2862, d3189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21596 (p : Pattern) (guard : d5502 p = 1) : d2863 p ≤ (0 : Int) + d3190 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2863, d3190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21595 p hg
    simpa only [d2863, d3190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2863, d3190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21572 p hg
    simpa only [d2863, d3190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21597 (p : Pattern) (guard : d5502 p = 1) : d2864 p ≤ (0 : Int) + d3191 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2864, d3191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21168 p hg
    simpa only [d2864, d3191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2864, d3191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2864, d3191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21598 (p : Pattern) (guard : d5502 p = 1) : d2865 p ≤ (0 : Int) + d3192 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2865, d3192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21596 p hg
    simpa only [d2865, d3192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2865, d3192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21597 p hg
    simpa only [d2865, d3192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21599 (p : Pattern) (guard : d5502 p = 1) : d2866 p ≤ (0 : Int) + d3193 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2866, d3193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21593 p hg
    simpa only [d2866, d3193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2866, d3193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21598 p hg
    simpa only [d2866, d3193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21600 (p : Pattern) (guard : d5502 p = 1) : d2867 p ≤ (0 : Int) + d3194 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2867, d3194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21575 p hg
    simpa only [d2867, d3194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2867, d3194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21599 p hg
    simpa only [d2867, d3194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21601 (p : Pattern) (guard : d5502 p = 1) : d2746 p ≤ (0 : Int) + d3195 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21415 p hg
    simpa only [d3195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21418 p hg
    simpa only [d3195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21602 (p : Pattern) (guard : d5502 p = 1) : d2868 p ≤ (0 : Int) + d3196 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2868, d3196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21425 p hg
    simpa only [d2868, d3196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2868, d3196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21200 p hg
    simpa only [d2868, d3196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21603 (p : Pattern) (guard : d5502 p = 1) : d2869 p ≤ (0 : Int) + d3197 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2869, d3197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21601 p hg
    simpa only [d2869, d3197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2869, d3197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21602 p hg
    simpa only [d2869, d3197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21604 (p : Pattern) (guard : d5502 p = 1) : d2870 p ≤ (0 : Int) + d3198 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2870, d3198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21603 p hg
    simpa only [d2870, d3198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2870, d3198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21437 p hg
    simpa only [d2870, d3198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21605 (p : Pattern) (guard : d5502 p = 1) : d2871 p ≤ (0 : Int) + d3199 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2871, d3199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21604 p hg
    simpa only [d2871, d3199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2871, d3199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21441 p hg
    simpa only [d2871, d3199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21606 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21607 (p : Pattern) (guard : d5502 p = 1) : d2703 p ≤ (0 : Int) + d2156 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2703, d2156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17336 p hg
    simpa only [d5502, d2703, d2156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2703, d2156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21606 p hg
    simpa only [d5502, d2703, d2156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21608 (p : Pattern) (guard : d5502 p = 1) : d2704 p ≤ (0 : Int) + d2157 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2704, d2157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21347 p hg
    simpa only [d2704, d2157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2704, d2157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21607 p hg
    simpa only [d2704, d2157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21609 (p : Pattern) (guard : d5502 p = 1) : d2705 p ≤ (0 : Int) + d2158 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2705, d2158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21608 p hg
    simpa only [d2705, d2158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2705, d2158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2705, d2158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21610 (p : Pattern) (guard : d5502 p = 1) : d2753 p ≤ (0 : Int) + d3200 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2753, d3200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21392 p hg
    simpa only [d2753, d3200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2753, d3200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21609 p hg
    simpa only [d2753, d3200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21611 (p : Pattern) (guard : d5502 p = 1) : d2753 p ≤ (0 : Int) + d3201 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21610 p hg
    simpa only [d3201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21425 p hg
    simpa only [d3201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21612 (p : Pattern) (guard : d5502 p = 1) : d2872 p ≤ (0 : Int) + d3202 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2872, d3202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21611 p hg
    simpa only [d2872, d3202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2872, d3202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21551 p hg
    simpa only [d2872, d3202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21613 (p : Pattern) (guard : d5502 p = 1) : d2873 p ≤ (0 : Int) + d3203 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2873, d3203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21612 p hg
    simpa only [d2873, d3203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2873, d3203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21440 p hg
    simpa only [d2873, d3203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21614 (p : Pattern) (guard : d5502 p = 1) : d2874 p ≤ (0 : Int) + d3204 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2874, d3204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21240 p hg
    simpa only [d2874, d3204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2874, d3204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2874, d3204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21615 (p : Pattern) (guard : d5502 p = 1) : d2875 p ≤ (0 : Int) + d3205 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2875, d3205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21614 p hg
    simpa only [d2875, d3205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2875, d3205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2875, d3205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21616 (p : Pattern) (guard : d5502 p = 1) : d2876 p ≤ (0 : Int) + d3206 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2876, d3206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21613 p hg
    simpa only [d2876, d3206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2876, d3206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d2876, d3206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21617 (p : Pattern) (guard : d5502 p = 1) : d2877 p ≤ (0 : Int) + d3207 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2877, d3207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21605 p hg
    simpa only [d2877, d3207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2877, d3207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d2877, d3207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21618 (p : Pattern) (guard : d5502 p = 1) : d2878 p ≤ (0 : Int) + d3208 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2878, d3208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21600 p hg
    simpa only [d2878, d3208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2878, d3208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d2878, d3208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21619 (p : Pattern) (guard : d5502 p = 1) : d2879 p ≤ (0 : Int) + d3209 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2879, d3209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21425 p hg
    simpa only [d2879, d3209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2879, d3209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21239 p hg
    simpa only [d2879, d3209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21620 (p : Pattern) (guard : d5502 p = 1) : d2880 p ≤ (0 : Int) + d3210 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2880, d3210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21601 p hg
    simpa only [d2880, d3210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2880, d3210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d2880, d3210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21621 (p : Pattern) (guard : d5502 p = 1) : d2881 p ≤ (0 : Int) + d3211 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2881, d3211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21420 p hg
    simpa only [d2881, d3211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2881, d3211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21239 p hg
    simpa only [d2881, d3211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21622 (p : Pattern) (guard : d5502 p = 1) : d2882 p ≤ (0 : Int) + d3212 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2882, d3212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21621 p hg
    simpa only [d2882, d3212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2882, d3212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2882, d3212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21623 (p : Pattern) (guard : d5502 p = 1) : d2883 p ≤ (0 : Int) + d3213 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2883, d3213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21620 p hg
    simpa only [d2883, d3213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2883, d3213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d2883, d3213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21624 (p : Pattern) (guard : d5502 p = 1) : d2884 p ≤ (0 : Int) + d3214 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2884, d3214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21428 p hg
    simpa only [d2884, d3214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2884, d3214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21200 p hg
    simpa only [d2884, d3214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21625 (p : Pattern) (guard : d5502 p = 1) : d2885 p ≤ (0 : Int) + d3215 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2885, d3215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21624 p hg
    simpa only [d2885, d3215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2885, d3215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2885, d3215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21626 (p : Pattern) (guard : d5502 p = 1) : d2886 p ≤ (0 : Int) + d3216 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2886, d3216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21625 p hg
    simpa only [d2886, d3216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2886, d3216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2886, d3216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21627 (p : Pattern) (guard : d5502 p = 1) : d2887 p ≤ (0 : Int) + d3217 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2887, d3217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21623 p hg
    simpa only [d2887, d3217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2887, d3217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21626 p hg
    simpa only [d2887, d3217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21628 (p : Pattern) (guard : d5502 p = 1) : d2888 p ≤ (0 : Int) + d3218 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2888, d3218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21627 p hg
    simpa only [d2888, d3218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2888, d3218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d2888, d3218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21629 (p : Pattern) (guard : d5502 p = 1) : d2889 p ≤ (0 : Int) + d3219 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2889, d3219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21628 p hg
    simpa only [d2889, d3219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2889, d3219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2889, d3219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21630 (p : Pattern) (guard : d5502 p = 1) : d2890 p ≤ (0 : Int) + d3220 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2890, d3220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d2890, d3220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2890, d3220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21629 p hg
    simpa only [d2890, d3220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21631 (p : Pattern) (guard : d5502 p = 1) : d2891 p ≤ (0 : Int) + d3221 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2891, d3221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21559 p hg
    simpa only [d2891, d3221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2891, d3221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21630 p hg
    simpa only [d2891, d3221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21632 (p : Pattern) (guard : d5502 p = 1) : d2892 p ≤ (0 : Int) + d3222 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2892, d3222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21285 p hg
    simpa only [d2892, d3222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2892, d3222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d2892, d3222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21633 (p : Pattern) (guard : d5502 p = 1) : d2893 p ≤ (0 : Int) + d3223 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2893, d3223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21540 p hg
    simpa only [d2893, d3223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2893, d3223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21632 p hg
    simpa only [d2893, d3223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21634 (p : Pattern) (guard : d5502 p = 1) : d2894 p ≤ (0 : Int) + d3224 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2894, d3224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21464 p hg
    simpa only [d2894, d3224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2894, d3224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21633 p hg
    simpa only [d2894, d3224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21635 (p : Pattern) (guard : d0 p = 1) : d2504 p ≤ (0 : Int) + d318 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21636 (p : Pattern) (guard : d5503 p = 1) : d2505 p ≤ (0 : Int) + d2184 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2505, d2184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21088 p hg
    simpa only [d5503, d2505, d2184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2505, d2184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d5503, d2505, d2184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21637 (p : Pattern) (guard : d0 p = 1) : d2506 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21638 (p : Pattern) (guard : d5503 p = 1) : d2507 p ≤ (0 : Int) + d2185 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2507, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21089 p hg
    simpa only [d5503, d2507, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2507, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21637 p hg
    simpa only [d5503, d2507, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21639 (p : Pattern) (guard : d5503 p = 1) : d2508 p ≤ (0 : Int) + d2186 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2508, d2186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21636 p hg
    simpa only [d2508, d2186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2508, d2186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21638 p hg
    simpa only [d2508, d2186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21640 (p : Pattern) (guard : d0 p = 1) : d2509 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21641 (p : Pattern) (guard : d5503 p = 1) : d2510 p ≤ (0 : Int) + d2185 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2510, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21089 p hg
    simpa only [d5503, d2510, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2510, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21640 p hg
    simpa only [d5503, d2510, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21642 (p : Pattern) (guard : d5503 p = 1) : d2511 p ≤ (0 : Int) + d2187 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2511, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21641 p hg
    simpa only [d2511, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2511, d2187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2511, d2187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21643 (p : Pattern) (guard : d5503 p = 1) : d2512 p ≤ (0 : Int) + d2188 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2512, d2188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21639 p hg
    simpa only [d2512, d2188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2512, d2188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21642 p hg
    simpa only [d2512, d2188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21644 (p : Pattern) (guard : d0 p = 1) : d2504 p ≤ (0 : Int) + d330 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21645 (p : Pattern) (guard : d5503 p = 1) : d2514 p ≤ (0 : Int) + d2189 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2514, d2189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21102 p hg
    simpa only [d5503, d2514, d2189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2514, d2189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21644 p hg
    simpa only [d5503, d2514, d2189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21646 (p : Pattern) (guard : d5503 p = 1) : d2515 p ≤ (0 : Int) + d2190 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2515, d2190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21645 p hg
    simpa only [d2515, d2190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2515, d2190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21638 p hg
    simpa only [d2515, d2190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21647 (p : Pattern) (guard : d5503 p = 1) : d2516 p ≤ (0 : Int) + d2191 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2516, d2191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21646 p hg
    simpa only [d2516, d2191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2516, d2191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21642 p hg
    simpa only [d2516, d2191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21648 (p : Pattern) (guard : d5503 p = 1) : d2517 p ≤ (0 : Int) + d2192 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2517, d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21643 p hg
    simpa only [d2517, d2192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2517, d2192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21647 p hg
    simpa only [d2517, d2192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21649 (p : Pattern) (guard : d0 p = 1) : d2504 p ≤ (0 : Int) + d332 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21650 (p : Pattern) (guard : d5503 p = 1) : d2504 p ≤ (0 : Int) + d2193 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21089 p hg
    simpa only [d5503, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21649 p hg
    simpa only [d5503, d2193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21651 (p : Pattern) (guard : d5503 p = 1) : d2518 p ≤ (0 : Int) + d2194 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2518, d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21650 p hg
    simpa only [d2518, d2194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2518, d2194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21638 p hg
    simpa only [d2518, d2194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21652 (p : Pattern) (guard : d5503 p = 1) : d2519 p ≤ (0 : Int) + d2195 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2519, d2195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d2519, d2195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2519, d2195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21642 p hg
    simpa only [d2519, d2195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21653 (p : Pattern) (guard : d0 p = 1) : d2520 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21654 (p : Pattern) (guard : d5503 p = 1) : d2520 p ≤ (0 : Int) + d2196 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21109 p hg
    simpa only [d5503, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21653 p hg
    simpa only [d5503, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21655 (p : Pattern) (guard : d0 p = 1) : d2521 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21656 (p : Pattern) (guard : d5503 p = 1) : d2522 p ≤ (0 : Int) + d2196 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2522, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21109 p hg
    simpa only [d5503, d2522, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2522, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21655 p hg
    simpa only [d5503, d2522, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21657 (p : Pattern) (guard : d5503 p = 1) : d2523 p ≤ (0 : Int) + d2196 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21654 p hg
    simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21656 p hg
    simpa only [d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21658 (p : Pattern) (guard : d0 p = 1) : d2524 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21659 (p : Pattern) (guard : d5503 p = 1) : d2525 p ≤ (0 : Int) + d2196 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2525, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21109 p hg
    simpa only [d5503, d2525, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2525, d2196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21658 p hg
    simpa only [d5503, d2525, d2196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21660 (p : Pattern) (guard : d5503 p = 1) : d2526 p ≤ (0 : Int) + d2197 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2526, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21659 p hg
    simpa only [d2526, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2526, d2197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2526, d2197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21661 (p : Pattern) (guard : d5503 p = 1) : d2527 p ≤ (0 : Int) + d2198 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2527, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21657 p hg
    simpa only [d2527, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2527, d2198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21660 p hg
    simpa only [d2527, d2198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21662 (p : Pattern) (guard : d5503 p = 1) : d2528 p ≤ (0 : Int) + d2199 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2528, d2199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21652 p hg
    simpa only [d2528, d2199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2528, d2199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21661 p hg
    simpa only [d2528, d2199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21663 (p : Pattern) (guard : d5503 p = 1) : d2529 p ≤ (0 : Int) + d2200 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2529, d2200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21648 p hg
    simpa only [d2529, d2200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2529, d2200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21662 p hg
    simpa only [d2529, d2200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21664 (p : Pattern) (guard : d0 p = 1) : d2504 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21665 (p : Pattern) (guard : d5503 p = 1) : d2504 p ≤ (0 : Int) + d2185 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21089 p hg
    simpa only [d5503, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21664 p hg
    simpa only [d5503, d2185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21666 (p : Pattern) (guard : d5503 p = 1) : d2518 p ≤ (0 : Int) + d2185 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21665 p hg
    simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21638 p hg
    simpa only [d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21667 (p : Pattern) (guard : d5503 p = 1) : d2519 p ≤ (0 : Int) + d2201 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2519, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21666 p hg
    simpa only [d2519, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2519, d2201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21642 p hg
    simpa only [d2519, d2201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21668 (p : Pattern) (guard : d5503 p = 1) : d2528 p ≤ (0 : Int) + d2202 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2528, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21667 p hg
    simpa only [d2528, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2528, d2202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21661 p hg
    simpa only [d2528, d2202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21669 (p : Pattern) (guard : d0 p = 1) : d2530 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21670 (p : Pattern) (guard : d5503 p = 1) : d2530 p ≤ (0 : Int) + d2203 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21121 p hg
    simpa only [d5503, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21669 p hg
    simpa only [d5503, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21671 (p : Pattern) (guard : d0 p = 1) : d357 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21672 (p : Pattern) (guard : d5503 p = 1) : d2531 p ≤ (0 : Int) + d2203 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2531, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21121 p hg
    simpa only [d5503, d2531, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2531, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21671 p hg
    simpa only [d5503, d2531, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21673 (p : Pattern) (guard : d5503 p = 1) : d2532 p ≤ (0 : Int) + d2203 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21670 p hg
    simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21672 p hg
    simpa only [d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21674 (p : Pattern) (guard : d0 p = 1) : d2533 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21675 (p : Pattern) (guard : d5503 p = 1) : d2534 p ≤ (0 : Int) + d2203 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2534, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21121 p hg
    simpa only [d5503, d2534, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2534, d2203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21674 p hg
    simpa only [d5503, d2534, d2203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21676 (p : Pattern) (guard : d5503 p = 1) : d2535 p ≤ (0 : Int) + d2204 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2535, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21675 p hg
    simpa only [d2535, d2204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2535, d2204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2535, d2204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21677 (p : Pattern) (guard : d5503 p = 1) : d2536 p ≤ (0 : Int) + d2205 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2536, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21673 p hg
    simpa only [d2536, d2205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2536, d2205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21676 p hg
    simpa only [d2536, d2205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21678 (p : Pattern) (guard : d5503 p = 1) : d2537 p ≤ (0 : Int) + d2206 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2537, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d2537, d2206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2537, d2206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2537, d2206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21679 (p : Pattern) (guard : d5503 p = 1) : d2538 p ≤ (0 : Int) + d2207 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2538, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21668 p hg
    simpa only [d2538, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2538, d2207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d2538, d2207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21680 (p : Pattern) (guard : d5503 p = 1) : d2539 p ≤ (0 : Int) + d2208 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2539, d2208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21663 p hg
    simpa only [d2539, d2208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2539, d2208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21679 p hg
    simpa only [d2539, d2208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21681 (p : Pattern) (guard : d0 p = 1) : d2541 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21682 (p : Pattern) (guard : d5503 p = 1) : d2542 p ≤ (0 : Int) + d2209 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2542, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21177 p hg
    simpa only [d5503, d2542, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2542, d2209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21681 p hg
    simpa only [d5503, d2542, d2209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21683 (p : Pattern) (guard : d5503 p = 1) : d2543 p ≤ (0 : Int) + d2210 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2543, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d2543, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2543, d2210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2543, d2210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21684 (p : Pattern) (guard : d5503 p = 1) : d2544 p ≤ (0 : Int) + d2211 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2544, d2211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21666 p hg
    simpa only [d2544, d2211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2544, d2211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21683 p hg
    simpa only [d2544, d2211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21685 (p : Pattern) (guard : d0 p = 1) : d2546 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21686 (p : Pattern) (guard : d5503 p = 1) : d2547 p ≤ (0 : Int) + d2212 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2547, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21244 p hg
    simpa only [d5503, d2547, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2547, d2212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21685 p hg
    simpa only [d5503, d2547, d2212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21687 (p : Pattern) (guard : d5503 p = 1) : d2548 p ≤ (0 : Int) + d2213 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2548, d2213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21686 p hg
    simpa only [d2548, d2213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2548, d2213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2548, d2213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21688 (p : Pattern) (guard : d5503 p = 1) : d2549 p ≤ (0 : Int) + d2214 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2549, d2214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21666 p hg
    simpa only [d2549, d2214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2549, d2214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21687 p hg
    simpa only [d2549, d2214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21689 (p : Pattern) (guard : d5503 p = 1) : d2550 p ≤ (0 : Int) + d2215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2550, d2215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21684 p hg
    simpa only [d2550, d2215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2550, d2215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21688 p hg
    simpa only [d2550, d2215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21690 (p : Pattern) (guard : d0 p = 1) : d332 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare21691 (p : Pattern) (guard : d5503 p = 1) : d2552 p ≤ (0 : Int) + d2216 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2552, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21198 p hg
    simpa only [d5503, d2552, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2552, d2216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21690 p hg
    simpa only [d5503, d2552, d2216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21692 (p : Pattern) (guard : d5503 p = 1) : d2553 p ≤ (0 : Int) + d2217 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2553, d2217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d2553, d2217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2553, d2217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2553, d2217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21693 (p : Pattern) (guard : d5503 p = 1) : d2554 p ≤ (0 : Int) + d2218 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2554, d2218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21666 p hg
    simpa only [d2554, d2218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2554, d2218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21692 p hg
    simpa only [d2554, d2218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21694 (p : Pattern) (guard : d5503 p = 1) : d2555 p ≤ (0 : Int) + d2219 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2555, d2219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21657 p hg
    simpa only [d2555, d2219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2555, d2219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2555, d2219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21695 (p : Pattern) (guard : d5503 p = 1) : d2556 p ≤ (0 : Int) + d2220 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2556, d2220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21693 p hg
    simpa only [d2556, d2220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2556, d2220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21694 p hg
    simpa only [d2556, d2220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21696 (p : Pattern) (guard : d5503 p = 1) : d2557 p ≤ (0 : Int) + d2221 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2557, d2221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21689 p hg
    simpa only [d2557, d2221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2557, d2221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21695 p hg
    simpa only [d2557, d2221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21697 (p : Pattern) (guard : d5503 p = 1) : d2558 p ≤ (0 : Int) + d2222 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2558, d2222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21666 p hg
    simpa only [d2558, d2222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2558, d2222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2558, d2222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21698 (p : Pattern) (guard : d5503 p = 1) : d2559 p ≤ (0 : Int) + d2223 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2559, d2223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21697 p hg
    simpa only [d2559, d2223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2559, d2223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21694 p hg
    simpa only [d2559, d2223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21699 (p : Pattern) (guard : d5503 p = 1) : d2560 p ≤ (0 : Int) + d2224 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2560, d2224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21673 p hg
    simpa only [d2560, d2224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2560, d2224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d2560, d2224, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
