/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons207
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare29120 (p : Pattern) (guard : d5855 p = 1) : d3461 p ≤ (0 : Int) + d2812 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29117 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29119 p hg
    simpa only [d5855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29121 (p : Pattern) (guard : d5854 p = 1) : d3461 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27742 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26892 p hg
    simpa only [d5854, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29122 (p : Pattern) (guard : d5855 p = 1) : d3461 p ≤ (0 : Int) + d2813 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5851 p = 1 := by simpa only [d5855, d2813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29117 p hg
    simpa only [d5855, d2813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d5855, d2813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29121 p hg
    simpa only [d5855, d2813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29123 (p : Pattern) (guard : d5855 p = 1) : d3461 p ≤ (0 : Int) + d2814 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29120 p hg
    simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29122 p hg
    simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29124 (p : Pattern) (guard : d5855 p = 1) : d3462 p ≤ (0 : Int) + d2815 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3462, d2815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29122 p hg
    simpa only [d3462, d2815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3462, d2815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3462, d2815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29125 (p : Pattern) (guard : d5855 p = 1) : d3463 p ≤ (0 : Int) + d2816 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3463, d2816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29123 p hg
    simpa only [d3463, d2816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3463, d2816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29124 p hg
    simpa only [d3463, d2816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29126 (p : Pattern) (guard : d5855 p = 1) : d3464 p ≤ (0 : Int) + d2817 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3464, d2817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28869 p hg
    simpa only [d3464, d2817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3464, d2817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29125 p hg
    simpa only [d3464, d2817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29127 (p : Pattern) (guard : d5855 p = 1) : d3465 p ≤ (0 : Int) + d2818 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3465, d2818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29126 p hg
    simpa only [d3465, d2818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3465, d2818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3465, d2818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29128 (p : Pattern) (guard : d5855 p = 1) : d3466 p ≤ (0 : Int) + d2819 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3466, d2819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29127 p hg
    simpa only [d3466, d2819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3466, d2819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3466, d2819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29129 (p : Pattern) (guard : d5855 p = 1) : d3467 p ≤ (0 : Int) + d2820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3467, d2820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29116 p hg
    simpa only [d3467, d2820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3467, d2820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29128 p hg
    simpa only [d3467, d2820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29130 (p : Pattern) (guard : d5855 p = 1) : d3468 p ≤ (0 : Int) + d2821 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3468, d2821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28869 p hg
    simpa only [d3468, d2821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3468, d2821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28850 p hg
    simpa only [d3468, d2821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29131 (p : Pattern) (guard : d5855 p = 1) : d3469 p ≤ (0 : Int) + d2822 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3469, d2822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28877 p hg
    simpa only [d3469, d2822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3469, d2822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29130 p hg
    simpa only [d3469, d2822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29132 (p : Pattern) (guard : d5855 p = 1) : d3470 p ≤ (0 : Int) + d2823 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3470, d2823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29131 p hg
    simpa only [d3470, d2823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3470, d2823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d3470, d2823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29133 (p : Pattern) (guard : d5855 p = 1) : d3471 p ≤ (0 : Int) + d2824 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3471, d2824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29125 p hg
    simpa only [d3471, d2824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3471, d2824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3471, d2824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29134 (p : Pattern) (guard : d5855 p = 1) : d3472 p ≤ (0 : Int) + d2825 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3472, d2825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29133 p hg
    simpa only [d3472, d2825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3472, d2825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3472, d2825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29135 (p : Pattern) (guard : d5855 p = 1) : d3473 p ≤ (0 : Int) + d2826 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3473, d2826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29134 p hg
    simpa only [d3473, d2826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3473, d2826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3473, d2826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29136 (p : Pattern) (guard : d5855 p = 1) : d3474 p ≤ (0 : Int) + d2827 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3474, d2827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29132 p hg
    simpa only [d3474, d2827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3474, d2827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29135 p hg
    simpa only [d3474, d2827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29137 (p : Pattern) (guard : d5855 p = 1) : d3475 p ≤ (0 : Int) + d2828 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3475, d2828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29129 p hg
    simpa only [d3475, d2828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3475, d2828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29136 p hg
    simpa only [d3475, d2828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29138 (p : Pattern) (guard : d5855 p = 1) : d3476 p ≤ (0 : Int) + d2829 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3476, d2829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29114 p hg
    simpa only [d3476, d2829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3476, d2829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29137 p hg
    simpa only [d3476, d2829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29139 (p : Pattern) (guard : d5855 p = 1) : d3477 p ≤ (0 : Int) + d2830 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3477, d2830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29137 p hg
    simpa only [d3477, d2830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3477, d2830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3477, d2830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29140 (p : Pattern) (guard : d5855 p = 1) : d3478 p ≤ (0 : Int) + d2831 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3478, d2831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29138 p hg
    simpa only [d3478, d2831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3478, d2831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29139 p hg
    simpa only [d3478, d2831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29141 (p : Pattern) (guard : d5855 p = 1) : d3479 p ≤ (0 : Int) + d2832 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3479, d2832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28937 p hg
    simpa only [d3479, d2832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3479, d2832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29140 p hg
    simpa only [d3479, d2832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29142 (p : Pattern) (guard : d5855 p = 1) : d3480 p ≤ (0 : Int) + d2833 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3480, d2833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28921 p hg
    simpa only [d3480, d2833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3480, d2833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29141 p hg
    simpa only [d3480, d2833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29143 (p : Pattern) (guard : d5855 p = 1) : d3481 p ≤ (0 : Int) + d2834 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3481, d2834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28985 p hg
    simpa only [d3481, d2834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3481, d2834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3481, d2834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29144 (p : Pattern) (guard : d5855 p = 1) : d3482 p ≤ (0 : Int) + d2835 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3482, d2835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29032 p hg
    simpa only [d3482, d2835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3482, d2835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29143 p hg
    simpa only [d3482, d2835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29145 (p : Pattern) (guard : d5855 p = 1) : d3483 p ≤ (0 : Int) + d2836 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3483, d2836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29143 p hg
    simpa only [d3483, d2836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3483, d2836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3483, d2836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29146 (p : Pattern) (guard : d5855 p = 1) : d3484 p ≤ (0 : Int) + d2837 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3484, d2837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29144 p hg
    simpa only [d3484, d2837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3484, d2837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29145 p hg
    simpa only [d3484, d2837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29147 (p : Pattern) (guard : d5855 p = 1) : d3485 p ≤ (0 : Int) + d2838 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3485, d2838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29009 p hg
    simpa only [d3485, d2838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3485, d2838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3485, d2838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29148 (p : Pattern) (guard : d5855 p = 1) : d3486 p ≤ (0 : Int) + d2839 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3486, d2839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29039 p hg
    simpa only [d3486, d2839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3486, d2839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29147 p hg
    simpa only [d3486, d2839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29149 (p : Pattern) (guard : d5855 p = 1) : d3487 p ≤ (0 : Int) + d2840 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3487, d2840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29147 p hg
    simpa only [d3487, d2840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3487, d2840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3487, d2840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29150 (p : Pattern) (guard : d5855 p = 1) : d3488 p ≤ (0 : Int) + d2841 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3488, d2841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29148 p hg
    simpa only [d3488, d2841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3488, d2841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29149 p hg
    simpa only [d3488, d2841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29151 (p : Pattern) (guard : d5855 p = 1) : d3489 p ≤ (0 : Int) + d2842 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3489, d2842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29146 p hg
    simpa only [d3489, d2842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3489, d2842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29150 p hg
    simpa only [d3489, d2842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29152 (p : Pattern) (guard : d5855 p = 1) : d3490 p ≤ (0 : Int) + d2843 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3490, d2843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29015 p hg
    simpa only [d3490, d2843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3490, d2843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29151 p hg
    simpa only [d3490, d2843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29153 (p : Pattern) (guard : d5855 p = 1) : d3481 p ≤ (0 : Int) + d2844 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3481, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29050 p hg
    simpa only [d3481, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3481, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3481, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29154 (p : Pattern) (guard : d5855 p = 1) : d3491 p ≤ (0 : Int) + d2845 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3491, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29065 p hg
    simpa only [d3491, d2845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3491, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29153 p hg
    simpa only [d3491, d2845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29155 (p : Pattern) (guard : d5855 p = 1) : d3483 p ≤ (0 : Int) + d2846 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3483, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29153 p hg
    simpa only [d3483, d2846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3483, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3483, d2846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29156 (p : Pattern) (guard : d5855 p = 1) : d3492 p ≤ (0 : Int) + d2847 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3492, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29154 p hg
    simpa only [d3492, d2847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3492, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29155 p hg
    simpa only [d3492, d2847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29157 (p : Pattern) (guard : d5855 p = 1) : d3493 p ≤ (0 : Int) + d2848 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3493, d2848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29156 p hg
    simpa only [d3493, d2848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3493, d2848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29073 p hg
    simpa only [d3493, d2848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29158 (p : Pattern) (guard : d5855 p = 1) : d3494 p ≤ (0 : Int) + d2849 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3494, d2849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29064 p hg
    simpa only [d3494, d2849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3494, d2849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29157 p hg
    simpa only [d3494, d2849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29159 (p : Pattern) (guard : d5855 p = 1) : d3495 p ≤ (0 : Int) + d2850 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3495, d2850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29152 p hg
    simpa only [d3495, d2850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3495, d2850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29158 p hg
    simpa only [d3495, d2850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29160 (p : Pattern) (guard : d5855 p = 1) : d3496 p ≤ (0 : Int) + d2851 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3496, d2851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29158 p hg
    simpa only [d3496, d2851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3496, d2851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29080 p hg
    simpa only [d3496, d2851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29161 (p : Pattern) (guard : d5855 p = 1) : d3497 p ≤ (0 : Int) + d2852 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3497, d2852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29159 p hg
    simpa only [d3497, d2852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3497, d2852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29160 p hg
    simpa only [d3497, d2852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29162 (p : Pattern) (guard : d5855 p = 1) : d3498 p ≤ (0 : Int) + d2853 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3498, d2853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29024 p hg
    simpa only [d3498, d2853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3498, d2853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29005 p hg
    simpa only [d3498, d2853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29163 (p : Pattern) (guard : d5855 p = 1) : d3499 p ≤ (0 : Int) + d2854 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3499, d2854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29055 p hg
    simpa only [d3499, d2854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3499, d2854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29162 p hg
    simpa only [d3499, d2854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29164 (p : Pattern) (guard : d5855 p = 1) : d3500 p ≤ (0 : Int) + d2855 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3500, d2855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29163 p hg
    simpa only [d3500, d2855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3500, d2855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29147 p hg
    simpa only [d3500, d2855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29165 (p : Pattern) (guard : d5855 p = 1) : d3501 p ≤ (0 : Int) + d2856 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3501, d2856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29059 p hg
    simpa only [d3501, d2856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3501, d2856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3501, d2856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29166 (p : Pattern) (guard : d5855 p = 1) : d3502 p ≤ (0 : Int) + d2857 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3502, d2857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29165 p hg
    simpa only [d3502, d2857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3502, d2857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3502, d2857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29167 (p : Pattern) (guard : d5855 p = 1) : d3503 p ≤ (0 : Int) + d2858 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3503, d2858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29166 p hg
    simpa only [d3503, d2858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3503, d2858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3503, d2858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29168 (p : Pattern) (guard : d5855 p = 1) : d3504 p ≤ (0 : Int) + d2859 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3504, d2859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29164 p hg
    simpa only [d3504, d2859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3504, d2859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29167 p hg
    simpa only [d3504, d2859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29169 (p : Pattern) (guard : d5855 p = 1) : d3505 p ≤ (0 : Int) + d2860 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3505, d2860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29054 p hg
    simpa only [d3505, d2860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3505, d2860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29168 p hg
    simpa only [d3505, d2860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29170 (p : Pattern) (guard : d5855 p = 1) : d3506 p ≤ (0 : Int) + d2861 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3506, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28978 p hg
    simpa only [d3506, d2861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3506, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29005 p hg
    simpa only [d3506, d2861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29171 (p : Pattern) (guard : d5855 p = 1) : d3507 p ≤ (0 : Int) + d2862 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3507, d2862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29170 p hg
    simpa only [d3507, d2862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3507, d2862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29009 p hg
    simpa only [d3507, d2862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29172 (p : Pattern) (guard : d5855 p = 1) : d3508 p ≤ (0 : Int) + d2863 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3508, d2863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29171 p hg
    simpa only [d3508, d2863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3508, d2863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29166 p hg
    simpa only [d3508, d2863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29173 (p : Pattern) (guard : d5855 p = 1) : d3509 p ≤ (0 : Int) + d2864 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3509, d2864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28813 p hg
    simpa only [d3509, d2864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3509, d2864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3509, d2864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29174 (p : Pattern) (guard : d5855 p = 1) : d3510 p ≤ (0 : Int) + d2865 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3510, d2865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29172 p hg
    simpa only [d3510, d2865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3510, d2865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29173 p hg
    simpa only [d3510, d2865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29175 (p : Pattern) (guard : d5855 p = 1) : d3511 p ≤ (0 : Int) + d2866 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3511, d2866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29156 p hg
    simpa only [d3511, d2866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3511, d2866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29174 p hg
    simpa only [d3511, d2866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29176 (p : Pattern) (guard : d5855 p = 1) : d3512 p ≤ (0 : Int) + d2867 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3512, d2867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29169 p hg
    simpa only [d3512, d2867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3512, d2867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29175 p hg
    simpa only [d3512, d2867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29177 (p : Pattern) (guard : d5855 p = 1) : d3513 p ≤ (0 : Int) + d2868 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3513, d2868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29055 p hg
    simpa only [d3513, d2868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3513, d2868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28850 p hg
    simpa only [d3513, d2868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29178 (p : Pattern) (guard : d5855 p = 1) : d3514 p ≤ (0 : Int) + d2869 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3514, d2869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29048 p hg
    simpa only [d3514, d2869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3514, d2869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29177 p hg
    simpa only [d3514, d2869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29179 (p : Pattern) (guard : d5855 p = 1) : d3515 p ≤ (0 : Int) + d2870 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3515, d2870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29178 p hg
    simpa only [d3515, d2870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3515, d2870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29069 p hg
    simpa only [d3515, d2870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29180 (p : Pattern) (guard : d5855 p = 1) : d3516 p ≤ (0 : Int) + d2871 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3516, d2871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29179 p hg
    simpa only [d3516, d2871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3516, d2871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29073 p hg
    simpa only [d3516, d2871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29181 (p : Pattern) (guard : d5855 p = 1) : d3517 p ≤ (0 : Int) + d2872 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3517, d2872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29055 p hg
    simpa only [d3517, d2872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3517, d2872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29153 p hg
    simpa only [d3517, d2872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29182 (p : Pattern) (guard : d5855 p = 1) : d3518 p ≤ (0 : Int) + d2873 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3518, d2873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29181 p hg
    simpa only [d3518, d2873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3518, d2873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29072 p hg
    simpa only [d3518, d2873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29183 (p : Pattern) (guard : d5855 p = 1) : d3519 p ≤ (0 : Int) + d2874 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3519, d2874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28874 p hg
    simpa only [d3519, d2874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3519, d2874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3519, d2874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29184 (p : Pattern) (guard : d5855 p = 1) : d3520 p ≤ (0 : Int) + d2875 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3520, d2875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29183 p hg
    simpa only [d3520, d2875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3520, d2875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3520, d2875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29185 (p : Pattern) (guard : d5855 p = 1) : d3521 p ≤ (0 : Int) + d2876 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3521, d2876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29182 p hg
    simpa only [d3521, d2876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3521, d2876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29184 p hg
    simpa only [d3521, d2876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29186 (p : Pattern) (guard : d5855 p = 1) : d3522 p ≤ (0 : Int) + d2877 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3522, d2877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29180 p hg
    simpa only [d3522, d2877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3522, d2877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29185 p hg
    simpa only [d3522, d2877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29187 (p : Pattern) (guard : d5855 p = 1) : d3523 p ≤ (0 : Int) + d2878 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3523, d2878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29176 p hg
    simpa only [d3523, d2878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3523, d2878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29186 p hg
    simpa only [d3523, d2878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29188 (p : Pattern) (guard : d5855 p = 1) : d3524 p ≤ (0 : Int) + d2879 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3524, d2879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29055 p hg
    simpa only [d3524, d2879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3524, d2879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28873 p hg
    simpa only [d3524, d2879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29189 (p : Pattern) (guard : d5855 p = 1) : d3525 p ≤ (0 : Int) + d2880 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3525, d2880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29048 p hg
    simpa only [d3525, d2880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3525, d2880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29188 p hg
    simpa only [d3525, d2880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29190 (p : Pattern) (guard : d5855 p = 1) : d3526 p ≤ (0 : Int) + d2881 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3526, d2881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29050 p hg
    simpa only [d3526, d2881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3526, d2881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28873 p hg
    simpa only [d3526, d2881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29191 (p : Pattern) (guard : d5855 p = 1) : d3527 p ≤ (0 : Int) + d2882 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3527, d2882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29190 p hg
    simpa only [d3527, d2882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3527, d2882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3527, d2882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29192 (p : Pattern) (guard : d5855 p = 1) : d3528 p ≤ (0 : Int) + d2883 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3528, d2883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29189 p hg
    simpa only [d3528, d2883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3528, d2883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29191 p hg
    simpa only [d3528, d2883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29193 (p : Pattern) (guard : d5855 p = 1) : d3529 p ≤ (0 : Int) + d2884 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3529, d2884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29060 p hg
    simpa only [d3529, d2884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3529, d2884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28850 p hg
    simpa only [d3529, d2884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29194 (p : Pattern) (guard : d5855 p = 1) : d3530 p ≤ (0 : Int) + d2885 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3530, d2885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29193 p hg
    simpa only [d3530, d2885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3530, d2885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3530, d2885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29195 (p : Pattern) (guard : d5855 p = 1) : d3531 p ≤ (0 : Int) + d2886 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3531, d2886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29194 p hg
    simpa only [d3531, d2886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3531, d2886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3531, d2886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29196 (p : Pattern) (guard : d5855 p = 1) : d3532 p ≤ (0 : Int) + d2887 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3532, d2887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29192 p hg
    simpa only [d3532, d2887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3532, d2887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29195 p hg
    simpa only [d3532, d2887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29197 (p : Pattern) (guard : d5855 p = 1) : d3533 p ≤ (0 : Int) + d2888 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3533, d2888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29196 p hg
    simpa only [d3533, d2888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3533, d2888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29185 p hg
    simpa only [d3533, d2888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29198 (p : Pattern) (guard : d5855 p = 1) : d3534 p ≤ (0 : Int) + d2889 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3534, d2889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29197 p hg
    simpa only [d3534, d2889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3534, d2889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d3534, d2889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29199 (p : Pattern) (guard : d5855 p = 1) : d3535 p ≤ (0 : Int) + d2890 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3535, d2890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29187 p hg
    simpa only [d3535, d2890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3535, d2890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29198 p hg
    simpa only [d3535, d2890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29200 (p : Pattern) (guard : d5855 p = 1) : d3536 p ≤ (0 : Int) + d2891 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3536, d2891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29161 p hg
    simpa only [d3536, d2891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3536, d2891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29199 p hg
    simpa only [d3536, d2891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29201 (p : Pattern) (guard : d5855 p = 1) : d3537 p ≤ (0 : Int) + d2892 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3537, d2892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28921 p hg
    simpa only [d3537, d2892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3537, d2892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29200 p hg
    simpa only [d3537, d2892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29202 (p : Pattern) (guard : d5855 p = 1) : d3538 p ≤ (0 : Int) + d2893 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3538, d2893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29142 p hg
    simpa only [d3538, d2893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3538, d2893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29201 p hg
    simpa only [d3538, d2893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29203 (p : Pattern) (guard : d5855 p = 1) : d3539 p ≤ (0 : Int) + d2894 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d3539, d2894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29096 p hg
    simpa only [d3539, d2894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d3539, d2894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29202 p hg
    simpa only [d3539, d2894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29204 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29205 (p : Pattern) (guard : d5843 p = 1) : d313 p ≤ (0 : Int) + d0 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29204 p hg
    simpa only [d5843, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29206 (p : Pattern) (guard : d5843 p = 1) : d3540 p ≤ (0 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3540, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29205 p hg
    simpa only [d3540, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3540, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19826 p hg
    simpa only [d3540, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29207 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d315 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29208 (p : Pattern) (guard : d5850 p = 1) : d3541 p ≤ (0 : Int) + d2503 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3541, d2503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29206 p hg
    simpa only [d5850, d3541, d2503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3541, d2503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29207 p hg
    simpa only [d5850, d3541, d2503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29209 (p : Pattern) (guard : d5843 p = 1) : d13 p ≤ (0 : Int) + d14 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26333 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19826 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29210 (p : Pattern) (guard : d5850 p = 1) : d13 p ≤ (0 : Int) + d2504 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d5850, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d5850, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29211 (p : Pattern) (guard : d5850 p = 1) : d3542 p ≤ (0 : Int) + d2505 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3542, d2505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29208 p hg
    simpa only [d3542, d2505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3542, d2505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29210 p hg
    simpa only [d3542, d2505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29212 (p : Pattern) (guard : d0 p = 1) : d3543 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29213 (p : Pattern) (guard : d5850 p = 1) : d3544 p ≤ (0 : Int) + d2504 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3544, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d5850, d3544, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3544, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29212 p hg
    simpa only [d5850, d3544, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29214 (p : Pattern) (guard : d5843 p = 1) : d13 p ≤ (0 : Int) + d1769 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d13, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d13, d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d13, d1769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26339 p hg
    simpa only [d5843, d13, d1769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29215 (p : Pattern) (guard : d5843 p = 1) : d3543 p ≤ (0 : Int) + d1770 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3543, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29214 p hg
    simpa only [d3543, d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3543, d1770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19861 p hg
    simpa only [d3543, d1770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29216 (p : Pattern) (guard : d5850 p = 1) : d3543 p ≤ (0 : Int) + d2506 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29215 p hg
    simpa only [d5850, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29212 p hg
    simpa only [d5850, d2506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29217 (p : Pattern) (guard : d5850 p = 1) : d3545 p ≤ (0 : Int) + d2507 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3545, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29213 p hg
    simpa only [d3545, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3545, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29216 p hg
    simpa only [d3545, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29218 (p : Pattern) (guard : d5850 p = 1) : d3546 p ≤ (0 : Int) + d2508 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3546, d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29211 p hg
    simpa only [d3546, d2508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3546, d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29217 p hg
    simpa only [d3546, d2508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29219 (p : Pattern) (guard : d0 p = 1) : d3547 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29220 (p : Pattern) (guard : d5850 p = 1) : d3548 p ≤ (0 : Int) + d2504 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3548, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d5850, d3548, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3548, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29219 p hg
    simpa only [d5850, d3548, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29221 (p : Pattern) (guard : d5843 p = 1) : d13 p ≤ (0 : Int) + d1683 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d13, d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d13, d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d13, d1683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26354 p hg
    simpa only [d5843, d13, d1683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29222 (p : Pattern) (guard : d5843 p = 1) : d3547 p ≤ (0 : Int) + d1684 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3547, d1684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29221 p hg
    simpa only [d3547, d1684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3547, d1684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19917 p hg
    simpa only [d3547, d1684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29223 (p : Pattern) (guard : d5850 p = 1) : d3547 p ≤ (0 : Int) + d2509 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29222 p hg
    simpa only [d5850, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29219 p hg
    simpa only [d5850, d2509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29224 (p : Pattern) (guard : d5850 p = 1) : d3549 p ≤ (0 : Int) + d2510 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3549, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29220 p hg
    simpa only [d3549, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3549, d2510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29223 p hg
    simpa only [d3549, d2510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29225 (p : Pattern) (guard : d5850 p = 1) : d3550 p ≤ (0 : Int) + d2511 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3550, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29224 p hg
    simpa only [d3550, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3550, d2511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3550, d2511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29226 (p : Pattern) (guard : d5850 p = 1) : d3551 p ≤ (0 : Int) + d2512 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3551, d2512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29218 p hg
    simpa only [d3551, d2512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3551, d2512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29225 p hg
    simpa only [d3551, d2512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29227 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d327 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29228 (p : Pattern) (guard : d5850 p = 1) : d13 p ≤ (0 : Int) + d2513 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d5850, d2513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29227 p hg
    simpa only [d5850, d2513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29229 (p : Pattern) (guard : d5850 p = 1) : d13 p ≤ (0 : Int) + d2514 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29228 p hg
    simpa only [d2514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d2514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29210 p hg
    simpa only [d2514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29230 (p : Pattern) (guard : d5850 p = 1) : d3552 p ≤ (0 : Int) + d2515 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3552, d2515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29229 p hg
    simpa only [d3552, d2515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3552, d2515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29217 p hg
    simpa only [d3552, d2515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29231 (p : Pattern) (guard : d5850 p = 1) : d3553 p ≤ (0 : Int) + d2516 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3553, d2516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29230 p hg
    simpa only [d3553, d2516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3553, d2516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29225 p hg
    simpa only [d3553, d2516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29232 (p : Pattern) (guard : d5850 p = 1) : d3554 p ≤ (0 : Int) + d2517 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3554, d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29226 p hg
    simpa only [d3554, d2517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3554, d2517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29231 p hg
    simpa only [d3554, d2517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29233 (p : Pattern) (guard : d5850 p = 1) : d3552 p ≤ (0 : Int) + d2518 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3552, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29210 p hg
    simpa only [d3552, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3552, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29217 p hg
    simpa only [d3552, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29234 (p : Pattern) (guard : d5850 p = 1) : d3553 p ≤ (0 : Int) + d2519 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3553, d2519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29233 p hg
    simpa only [d3553, d2519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3553, d2519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29225 p hg
    simpa only [d3553, d2519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29235 (p : Pattern) (guard : d5843 p = 1) : d17 p ≤ (0 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26340 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19861 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29236 (p : Pattern) (guard : d5850 p = 1) : d17 p ≤ (0 : Int) + d2520 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29235 p hg
    simpa only [d5850, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d5850, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29237 (p : Pattern) (guard : d0 p = 1) : d3555 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29238 (p : Pattern) (guard : d5850 p = 1) : d3556 p ≤ (0 : Int) + d2520 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3556, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29235 p hg
    simpa only [d5850, d3556, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3556, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29237 p hg
    simpa only [d5850, d3556, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29239 (p : Pattern) (guard : d5843 p = 1) : d17 p ≤ (0 : Int) + d1794 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d17, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14537 p hg
    simpa only [d5843, d17, d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d17, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23784 p hg
    simpa only [d5843, d17, d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29240 (p : Pattern) (guard : d5843 p = 1) : d3555 p ≤ (0 : Int) + d1795 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3555, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29239 p hg
    simpa only [d3555, d1795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3555, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20378 p hg
    simpa only [d3555, d1795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29241 (p : Pattern) (guard : d5850 p = 1) : d3555 p ≤ (0 : Int) + d2521 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29240 p hg
    simpa only [d5850, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29237 p hg
    simpa only [d5850, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29242 (p : Pattern) (guard : d5850 p = 1) : d3557 p ≤ (0 : Int) + d2522 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3557, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29238 p hg
    simpa only [d3557, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3557, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29241 p hg
    simpa only [d3557, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29243 (p : Pattern) (guard : d5850 p = 1) : d3558 p ≤ (0 : Int) + d2523 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3558, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29236 p hg
    simpa only [d3558, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3558, d2523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29242 p hg
    simpa only [d3558, d2523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29244 (p : Pattern) (guard : d0 p = 1) : d3559 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare29245 (p : Pattern) (guard : d5850 p = 1) : d3560 p ≤ (0 : Int) + d2520 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3560, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29235 p hg
    simpa only [d5850, d3560, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3560, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29244 p hg
    simpa only [d5850, d3560, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29246 (p : Pattern) (guard : d5843 p = 1) : d17 p ≤ (0 : Int) + d1693 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d17, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14537 p hg
    simpa only [d5843, d17, d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d17, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26360 p hg
    simpa only [d5843, d17, d1693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29247 (p : Pattern) (guard : d5843 p = 1) : d3559 p ≤ (0 : Int) + d1694 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3559, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29246 p hg
    simpa only [d3559, d1694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3559, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19928 p hg
    simpa only [d3559, d1694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29248 (p : Pattern) (guard : d5850 p = 1) : d3559 p ≤ (0 : Int) + d2524 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29247 p hg
    simpa only [d5850, d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29244 p hg
    simpa only [d5850, d2524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29249 (p : Pattern) (guard : d5850 p = 1) : d3561 p ≤ (0 : Int) + d2525 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3561, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29245 p hg
    simpa only [d3561, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3561, d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29248 p hg
    simpa only [d3561, d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29250 (p : Pattern) (guard : d5850 p = 1) : d3562 p ≤ (0 : Int) + d2526 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3562, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29249 p hg
    simpa only [d3562, d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3562, d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20523 p hg
    simpa only [d3562, d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29251 (p : Pattern) (guard : d5850 p = 1) : d3563 p ≤ (0 : Int) + d2527 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3563, d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29243 p hg
    simpa only [d3563, d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3563, d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29250 p hg
    simpa only [d3563, d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29252 (p : Pattern) (guard : d5850 p = 1) : d3564 p ≤ (0 : Int) + d2528 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3564, d2528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29234 p hg
    simpa only [d3564, d2528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3564, d2528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29251 p hg
    simpa only [d3564, d2528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29253 (p : Pattern) (guard : d5850 p = 1) : d3565 p ≤ (0 : Int) + d2529 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3565, d2529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29232 p hg
    simpa only [d3565, d2529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3565, d2529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29252 p hg
    simpa only [d3565, d2529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29254 (p : Pattern) (guard : d5843 p = 1) : d23 p ≤ (0 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23418 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19889 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29255 (p : Pattern) (guard : d5850 p = 1) : d23 p ≤ (0 : Int) + d2530 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29254 p hg
    simpa only [d5850, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5850, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29256 (p : Pattern) (guard : d5850 p = 1) : d3566 p ≤ (0 : Int) + d2530 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d3566, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29254 p hg
    simpa only [d5850, d3566, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d3566, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17230 p hg
    simpa only [d5850, d3566, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29257 (p : Pattern) (guard : d5850 p = 1) : d356 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5850, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20552 p hg
    simpa only [d5850, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5850, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17230 p hg
    simpa only [d5850, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29258 (p : Pattern) (guard : d5850 p = 1) : d3567 p ≤ (0 : Int) + d2531 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3567, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29256 p hg
    simpa only [d3567, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3567, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29257 p hg
    simpa only [d3567, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29259 (p : Pattern) (guard : d5850 p = 1) : d3568 p ≤ (0 : Int) + d2532 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5850 p = 1 := by simpa only [d3568, d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29255 p hg
    simpa only [d3568, d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5850 p = 1 := by simpa only [d3568, d2532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29258 p hg
    simpa only [d3568, d2532, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
