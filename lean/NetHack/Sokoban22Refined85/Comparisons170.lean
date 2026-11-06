/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons169
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare23800 (p : Pattern) (guard : d5855 p = 1) : d2825 p ≤ (0 : Int) + d3472 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2825, d3472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23799 p hg
    simpa only [d2825, d3472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2825, d3472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2825, d3472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23801 (p : Pattern) (guard : d5855 p = 1) : d2826 p ≤ (0 : Int) + d3473 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2826, d3473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23800 p hg
    simpa only [d2826, d3473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2826, d3473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2826, d3473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23802 (p : Pattern) (guard : d5855 p = 1) : d2827 p ≤ (0 : Int) + d3474 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2827, d3474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23798 p hg
    simpa only [d2827, d3474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2827, d3474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23801 p hg
    simpa only [d2827, d3474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23803 (p : Pattern) (guard : d5855 p = 1) : d2828 p ≤ (0 : Int) + d3475 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2828, d3475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23795 p hg
    simpa only [d2828, d3475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2828, d3475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23802 p hg
    simpa only [d2828, d3475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23804 (p : Pattern) (guard : d5855 p = 1) : d2829 p ≤ (0 : Int) + d3476 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2829, d3476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23776 p hg
    simpa only [d2829, d3476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2829, d3476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23803 p hg
    simpa only [d2829, d3476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23805 (p : Pattern) (guard : d5855 p = 1) : d2830 p ≤ (0 : Int) + d3477 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2830, d3477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23803 p hg
    simpa only [d2830, d3477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2830, d3477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2830, d3477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23806 (p : Pattern) (guard : d5855 p = 1) : d2831 p ≤ (0 : Int) + d3478 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2831, d3478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23804 p hg
    simpa only [d2831, d3478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2831, d3478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23805 p hg
    simpa only [d2831, d3478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23807 (p : Pattern) (guard : d5855 p = 1) : d2832 p ≤ (0 : Int) + d3479 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2832, d3479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23595 p hg
    simpa only [d2832, d3479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2832, d3479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23806 p hg
    simpa only [d2832, d3479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23808 (p : Pattern) (guard : d5855 p = 1) : d2833 p ≤ (0 : Int) + d3480 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2833, d3480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23579 p hg
    simpa only [d2833, d3480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2833, d3480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23807 p hg
    simpa only [d2833, d3480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23809 (p : Pattern) (guard : d5855 p = 1) : d2834 p ≤ (0 : Int) + d3481 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2834, d3481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23645 p hg
    simpa only [d2834, d3481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2834, d3481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2834, d3481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23810 (p : Pattern) (guard : d5855 p = 1) : d2835 p ≤ (0 : Int) + d3482 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2835, d3482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23693 p hg
    simpa only [d2835, d3482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2835, d3482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23809 p hg
    simpa only [d2835, d3482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23811 (p : Pattern) (guard : d5855 p = 1) : d2836 p ≤ (0 : Int) + d3483 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2836, d3483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23809 p hg
    simpa only [d2836, d3483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2836, d3483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2836, d3483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23812 (p : Pattern) (guard : d5855 p = 1) : d2837 p ≤ (0 : Int) + d3484 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2837, d3484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23810 p hg
    simpa only [d2837, d3484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2837, d3484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23811 p hg
    simpa only [d2837, d3484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23813 (p : Pattern) (guard : d5855 p = 1) : d2838 p ≤ (0 : Int) + d3485 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2838, d3485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23669 p hg
    simpa only [d2838, d3485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2838, d3485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2838, d3485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23814 (p : Pattern) (guard : d5855 p = 1) : d2839 p ≤ (0 : Int) + d3486 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2839, d3486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23700 p hg
    simpa only [d2839, d3486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2839, d3486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23813 p hg
    simpa only [d2839, d3486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23815 (p : Pattern) (guard : d5855 p = 1) : d2840 p ≤ (0 : Int) + d3487 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2840, d3487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23813 p hg
    simpa only [d2840, d3487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2840, d3487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2840, d3487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23816 (p : Pattern) (guard : d5855 p = 1) : d2841 p ≤ (0 : Int) + d3488 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2841, d3488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23814 p hg
    simpa only [d2841, d3488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2841, d3488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23815 p hg
    simpa only [d2841, d3488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23817 (p : Pattern) (guard : d5855 p = 1) : d2842 p ≤ (0 : Int) + d3489 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2842, d3489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23812 p hg
    simpa only [d2842, d3489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2842, d3489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23816 p hg
    simpa only [d2842, d3489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23818 (p : Pattern) (guard : d5855 p = 1) : d2843 p ≤ (0 : Int) + d3490 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2843, d3490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23675 p hg
    simpa only [d2843, d3490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2843, d3490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23817 p hg
    simpa only [d2843, d3490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23819 (p : Pattern) (guard : d5855 p = 1) : d2844 p ≤ (0 : Int) + d3481 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2844, d3481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23711 p hg
    simpa only [d2844, d3481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2844, d3481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2844, d3481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23820 (p : Pattern) (guard : d5855 p = 1) : d2845 p ≤ (0 : Int) + d3491 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2845, d3491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23727 p hg
    simpa only [d2845, d3491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2845, d3491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23819 p hg
    simpa only [d2845, d3491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23821 (p : Pattern) (guard : d5855 p = 1) : d2846 p ≤ (0 : Int) + d3483 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2846, d3483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23819 p hg
    simpa only [d2846, d3483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2846, d3483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2846, d3483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23822 (p : Pattern) (guard : d5855 p = 1) : d2847 p ≤ (0 : Int) + d3492 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2847, d3492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23820 p hg
    simpa only [d2847, d3492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2847, d3492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23821 p hg
    simpa only [d2847, d3492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23823 (p : Pattern) (guard : d5855 p = 1) : d2848 p ≤ (0 : Int) + d3493 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2848, d3493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23822 p hg
    simpa only [d2848, d3493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2848, d3493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23735 p hg
    simpa only [d2848, d3493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23824 (p : Pattern) (guard : d5855 p = 1) : d2849 p ≤ (0 : Int) + d3494 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2849, d3494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23726 p hg
    simpa only [d2849, d3494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2849, d3494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23823 p hg
    simpa only [d2849, d3494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23825 (p : Pattern) (guard : d5855 p = 1) : d2850 p ≤ (0 : Int) + d3495 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2850, d3495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23818 p hg
    simpa only [d2850, d3495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2850, d3495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23824 p hg
    simpa only [d2850, d3495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23826 (p : Pattern) (guard : d5855 p = 1) : d2851 p ≤ (0 : Int) + d3496 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2851, d3496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23824 p hg
    simpa only [d2851, d3496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2851, d3496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23742 p hg
    simpa only [d2851, d3496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23827 (p : Pattern) (guard : d5855 p = 1) : d2852 p ≤ (0 : Int) + d3497 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2852, d3497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23825 p hg
    simpa only [d2852, d3497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2852, d3497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23826 p hg
    simpa only [d2852, d3497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23828 (p : Pattern) (guard : d5855 p = 1) : d2853 p ≤ (0 : Int) + d3498 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2853, d3498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23685 p hg
    simpa only [d2853, d3498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2853, d3498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23665 p hg
    simpa only [d2853, d3498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23829 (p : Pattern) (guard : d5855 p = 1) : d2854 p ≤ (0 : Int) + d3499 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2854, d3499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23716 p hg
    simpa only [d2854, d3499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2854, d3499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23828 p hg
    simpa only [d2854, d3499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23830 (p : Pattern) (guard : d5855 p = 1) : d2855 p ≤ (0 : Int) + d3500 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2855, d3500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23829 p hg
    simpa only [d2855, d3500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2855, d3500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23813 p hg
    simpa only [d2855, d3500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23831 (p : Pattern) (guard : d5855 p = 1) : d2856 p ≤ (0 : Int) + d3501 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2856, d3501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23721 p hg
    simpa only [d2856, d3501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2856, d3501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2856, d3501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23832 (p : Pattern) (guard : d5855 p = 1) : d2857 p ≤ (0 : Int) + d3502 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2857, d3502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23831 p hg
    simpa only [d2857, d3502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2857, d3502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2857, d3502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23833 (p : Pattern) (guard : d5855 p = 1) : d2858 p ≤ (0 : Int) + d3503 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2858, d3503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23832 p hg
    simpa only [d2858, d3503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2858, d3503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2858, d3503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23834 (p : Pattern) (guard : d5855 p = 1) : d2859 p ≤ (0 : Int) + d3504 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2859, d3504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23830 p hg
    simpa only [d2859, d3504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2859, d3504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23833 p hg
    simpa only [d2859, d3504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23835 (p : Pattern) (guard : d5855 p = 1) : d2860 p ≤ (0 : Int) + d3505 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2860, d3505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23715 p hg
    simpa only [d2860, d3505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2860, d3505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23834 p hg
    simpa only [d2860, d3505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23836 (p : Pattern) (guard : d5855 p = 1) : d2861 p ≤ (0 : Int) + d3506 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2861, d3506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23638 p hg
    simpa only [d2861, d3506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2861, d3506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23665 p hg
    simpa only [d2861, d3506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23837 (p : Pattern) (guard : d5855 p = 1) : d2862 p ≤ (0 : Int) + d3507 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2862, d3507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23836 p hg
    simpa only [d2862, d3507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2862, d3507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23669 p hg
    simpa only [d2862, d3507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23838 (p : Pattern) (guard : d5855 p = 1) : d2863 p ≤ (0 : Int) + d3508 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2863, d3508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23837 p hg
    simpa only [d2863, d3508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2863, d3508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23832 p hg
    simpa only [d2863, d3508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23839 (p : Pattern) (guard : d5855 p = 1) : d2864 p ≤ (0 : Int) + d3509 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2864, d3509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23464 p hg
    simpa only [d2864, d3509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2864, d3509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2864, d3509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23840 (p : Pattern) (guard : d5855 p = 1) : d2865 p ≤ (0 : Int) + d3510 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2865, d3510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23838 p hg
    simpa only [d2865, d3510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2865, d3510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23839 p hg
    simpa only [d2865, d3510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23841 (p : Pattern) (guard : d5855 p = 1) : d2866 p ≤ (0 : Int) + d3511 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2866, d3511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23822 p hg
    simpa only [d2866, d3511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2866, d3511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23840 p hg
    simpa only [d2866, d3511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23842 (p : Pattern) (guard : d5855 p = 1) : d2867 p ≤ (0 : Int) + d3512 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2867, d3512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23835 p hg
    simpa only [d2867, d3512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2867, d3512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23841 p hg
    simpa only [d2867, d3512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23843 (p : Pattern) (guard : d5855 p = 1) : d2868 p ≤ (0 : Int) + d3513 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2868, d3513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23716 p hg
    simpa only [d2868, d3513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2868, d3513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23507 p hg
    simpa only [d2868, d3513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23844 (p : Pattern) (guard : d5855 p = 1) : d2869 p ≤ (0 : Int) + d3514 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2869, d3514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23709 p hg
    simpa only [d2869, d3514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2869, d3514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23843 p hg
    simpa only [d2869, d3514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23845 (p : Pattern) (guard : d5855 p = 1) : d2870 p ≤ (0 : Int) + d3515 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2870, d3515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23844 p hg
    simpa only [d2870, d3515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2870, d3515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23731 p hg
    simpa only [d2870, d3515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23846 (p : Pattern) (guard : d5855 p = 1) : d2871 p ≤ (0 : Int) + d3516 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2871, d3516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23845 p hg
    simpa only [d2871, d3516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2871, d3516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23735 p hg
    simpa only [d2871, d3516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23847 (p : Pattern) (guard : d5855 p = 1) : d2872 p ≤ (0 : Int) + d3517 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2872, d3517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23716 p hg
    simpa only [d2872, d3517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2872, d3517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23819 p hg
    simpa only [d2872, d3517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23848 (p : Pattern) (guard : d5855 p = 1) : d2873 p ≤ (0 : Int) + d3518 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2873, d3518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23847 p hg
    simpa only [d2873, d3518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2873, d3518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23734 p hg
    simpa only [d2873, d3518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23849 (p : Pattern) (guard : d5855 p = 1) : d2874 p ≤ (0 : Int) + d3519 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2874, d3519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23531 p hg
    simpa only [d2874, d3519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2874, d3519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2874, d3519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23850 (p : Pattern) (guard : d5855 p = 1) : d2875 p ≤ (0 : Int) + d3520 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2875, d3520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23849 p hg
    simpa only [d2875, d3520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2875, d3520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2875, d3520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23851 (p : Pattern) (guard : d5855 p = 1) : d2876 p ≤ (0 : Int) + d3521 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2876, d3521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23848 p hg
    simpa only [d2876, d3521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2876, d3521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23850 p hg
    simpa only [d2876, d3521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23852 (p : Pattern) (guard : d5855 p = 1) : d2877 p ≤ (0 : Int) + d3522 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2877, d3522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23846 p hg
    simpa only [d2877, d3522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2877, d3522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23851 p hg
    simpa only [d2877, d3522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23853 (p : Pattern) (guard : d5855 p = 1) : d2878 p ≤ (0 : Int) + d3523 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2878, d3523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23842 p hg
    simpa only [d2878, d3523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2878, d3523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23852 p hg
    simpa only [d2878, d3523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23854 (p : Pattern) (guard : d5855 p = 1) : d2879 p ≤ (0 : Int) + d3524 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2879, d3524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23716 p hg
    simpa only [d2879, d3524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2879, d3524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23530 p hg
    simpa only [d2879, d3524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23855 (p : Pattern) (guard : d5855 p = 1) : d2880 p ≤ (0 : Int) + d3525 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2880, d3525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23709 p hg
    simpa only [d2880, d3525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2880, d3525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23854 p hg
    simpa only [d2880, d3525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23856 (p : Pattern) (guard : d5855 p = 1) : d2881 p ≤ (0 : Int) + d3526 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2881, d3526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23711 p hg
    simpa only [d2881, d3526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2881, d3526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23530 p hg
    simpa only [d2881, d3526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23857 (p : Pattern) (guard : d5855 p = 1) : d2882 p ≤ (0 : Int) + d3527 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2882, d3527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23856 p hg
    simpa only [d2882, d3527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2882, d3527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2882, d3527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23858 (p : Pattern) (guard : d5855 p = 1) : d2883 p ≤ (0 : Int) + d3528 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2883, d3528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23855 p hg
    simpa only [d2883, d3528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2883, d3528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23857 p hg
    simpa only [d2883, d3528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23859 (p : Pattern) (guard : d5855 p = 1) : d2884 p ≤ (0 : Int) + d3529 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2884, d3529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23722 p hg
    simpa only [d2884, d3529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2884, d3529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23507 p hg
    simpa only [d2884, d3529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23860 (p : Pattern) (guard : d5855 p = 1) : d2885 p ≤ (0 : Int) + d3530 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2885, d3530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23859 p hg
    simpa only [d2885, d3530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2885, d3530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2885, d3530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23861 (p : Pattern) (guard : d5855 p = 1) : d2886 p ≤ (0 : Int) + d3531 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2886, d3531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23860 p hg
    simpa only [d2886, d3531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2886, d3531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2886, d3531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23862 (p : Pattern) (guard : d5855 p = 1) : d2887 p ≤ (0 : Int) + d3532 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2887, d3532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23858 p hg
    simpa only [d2887, d3532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2887, d3532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23861 p hg
    simpa only [d2887, d3532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23863 (p : Pattern) (guard : d5855 p = 1) : d2888 p ≤ (0 : Int) + d3533 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2888, d3533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23862 p hg
    simpa only [d2888, d3533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2888, d3533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23851 p hg
    simpa only [d2888, d3533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23864 (p : Pattern) (guard : d5855 p = 1) : d2889 p ≤ (0 : Int) + d3534 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2889, d3534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23863 p hg
    simpa only [d2889, d3534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2889, d3534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d2889, d3534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23865 (p : Pattern) (guard : d5855 p = 1) : d2890 p ≤ (0 : Int) + d3535 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2890, d3535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23853 p hg
    simpa only [d2890, d3535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2890, d3535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23864 p hg
    simpa only [d2890, d3535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23866 (p : Pattern) (guard : d5855 p = 1) : d2891 p ≤ (0 : Int) + d3536 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2891, d3536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23827 p hg
    simpa only [d2891, d3536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2891, d3536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23865 p hg
    simpa only [d2891, d3536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23867 (p : Pattern) (guard : d5855 p = 1) : d2892 p ≤ (0 : Int) + d3537 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2892, d3537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23579 p hg
    simpa only [d2892, d3537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2892, d3537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23866 p hg
    simpa only [d2892, d3537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23868 (p : Pattern) (guard : d5855 p = 1) : d2893 p ≤ (0 : Int) + d3538 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2893, d3538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23808 p hg
    simpa only [d2893, d3538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2893, d3538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23867 p hg
    simpa only [d2893, d3538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23869 (p : Pattern) (guard : d5855 p = 1) : d2894 p ≤ (0 : Int) + d3539 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5855 p = 1 := by simpa only [d2894, d3539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23758 p hg
    simpa only [d2894, d3539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5855 p = 1 := by simpa only [d2894, d3539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23868 p hg
    simpa only [d2894, d3539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23870 (p : Pattern) (guard : d0 p = 1) : d1772 p ≤ (0 : Int) + d321 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23871 (p : Pattern) (guard : d4474 p = 1) : d2895 p ≤ (0 : Int) + d1682 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2895, d1682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d2895, d1682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2895, d1682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23870 p hg
    simpa only [d4474, d2895, d1682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23872 (p : Pattern) (guard : d4474 p = 1) : d2896 p ≤ (0 : Int) + d1688 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2896, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23871 p hg
    simpa only [d2896, d1688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2896, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16330 p hg
    simpa only [d2896, d1688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23873 (p : Pattern) (guard : d0 p = 1) : d1772 p ≤ (0 : Int) + d333 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23874 (p : Pattern) (guard : d4474 p = 1) : d2895 p ≤ (0 : Int) + d1689 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2895, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d2895, d1689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2895, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23873 p hg
    simpa only [d4474, d2895, d1689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23875 (p : Pattern) (guard : d4474 p = 1) : d2896 p ≤ (0 : Int) + d1690 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2896, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23874 p hg
    simpa only [d2896, d1690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2896, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16330 p hg
    simpa only [d2896, d1690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23876 (p : Pattern) (guard : d4474 p = 1) : d2896 p ≤ (0 : Int) + d1691 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23872 p hg
    simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23875 p hg
    simpa only [d1691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23877 (p : Pattern) (guard : d0 p = 1) : d1772 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23878 (p : Pattern) (guard : d4474 p = 1) : d2895 p ≤ (0 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2895, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d2895, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2895, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23877 p hg
    simpa only [d4474, d2895, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23879 (p : Pattern) (guard : d4474 p = 1) : d2896 p ≤ (0 : Int) + d1692 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2896, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23878 p hg
    simpa only [d2896, d1692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2896, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16330 p hg
    simpa only [d2896, d1692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23880 (p : Pattern) (guard : d0 p = 1) : d2012 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23881 (p : Pattern) (guard : d4474 p = 1) : d2897 p ≤ (0 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2897, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d4474, d2897, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2897, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23880 p hg
    simpa only [d4474, d2897, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23882 (p : Pattern) (guard : d4474 p = 1) : d2898 p ≤ (0 : Int) + d1698 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2898, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23881 p hg
    simpa only [d2898, d1698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2898, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16339 p hg
    simpa only [d2898, d1698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23883 (p : Pattern) (guard : d4474 p = 1) : d2899 p ≤ (0 : Int) + d1699 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2899, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23879 p hg
    simpa only [d2899, d1699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2899, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23882 p hg
    simpa only [d2899, d1699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23884 (p : Pattern) (guard : d4474 p = 1) : d2900 p ≤ (0 : Int) + d1700 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2900, d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23876 p hg
    simpa only [d2900, d1700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2900, d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23883 p hg
    simpa only [d2900, d1700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23885 (p : Pattern) (guard : d0 p = 1) : d1803 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23886 (p : Pattern) (guard : d4474 p = 1) : d2901 p ≤ (0 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2901, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d4474, d2901, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2901, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23885 p hg
    simpa only [d4474, d2901, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23887 (p : Pattern) (guard : d4474 p = 1) : d2902 p ≤ (0 : Int) + d1706 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2902, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23886 p hg
    simpa only [d2902, d1706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2902, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16344 p hg
    simpa only [d2902, d1706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23888 (p : Pattern) (guard : d4474 p = 1) : d2903 p ≤ (0 : Int) + d1707 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2903, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23887 p hg
    simpa only [d2903, d1707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2903, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2903, d1707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23889 (p : Pattern) (guard : d4474 p = 1) : d2904 p ≤ (0 : Int) + d1708 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2904, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23883 p hg
    simpa only [d2904, d1708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2904, d1708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23888 p hg
    simpa only [d2904, d1708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23890 (p : Pattern) (guard : d4474 p = 1) : d2905 p ≤ (0 : Int) + d1709 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2905, d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23884 p hg
    simpa only [d2905, d1709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2905, d1709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23889 p hg
    simpa only [d2905, d1709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23891 (p : Pattern) (guard : d0 p = 1) : d1788 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23892 (p : Pattern) (guard : d4474 p = 1) : d2906 p ≤ (0 : Int) + d15 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2906, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d2906, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2906, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23891 p hg
    simpa only [d4474, d2906, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23893 (p : Pattern) (guard : d4474 p = 1) : d2907 p ≤ (0 : Int) + d1719 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2907, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23892 p hg
    simpa only [d2907, d1719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2907, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16351 p hg
    simpa only [d2907, d1719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23894 (p : Pattern) (guard : d4474 p = 1) : d2908 p ≤ (0 : Int) + d1726 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2908, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23892 p hg
    simpa only [d2908, d1726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2908, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16353 p hg
    simpa only [d2908, d1726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23895 (p : Pattern) (guard : d4474 p = 1) : d2909 p ≤ (0 : Int) + d1727 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2909, d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23893 p hg
    simpa only [d2909, d1727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2909, d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23894 p hg
    simpa only [d2909, d1727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23896 (p : Pattern) (guard : d4474 p = 1) : d2910 p ≤ (0 : Int) + d1731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2910, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23892 p hg
    simpa only [d2910, d1731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2910, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16356 p hg
    simpa only [d2910, d1731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23897 (p : Pattern) (guard : d0 p = 1) : d1797 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23898 (p : Pattern) (guard : d4474 p = 1) : d2911 p ≤ (0 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2911, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d4474, d2911, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2911, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23897 p hg
    simpa only [d4474, d2911, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23899 (p : Pattern) (guard : d4474 p = 1) : d2912 p ≤ (0 : Int) + d1732 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2912, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23898 p hg
    simpa only [d2912, d1732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2912, d1732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2912, d1732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23900 (p : Pattern) (guard : d4474 p = 1) : d2913 p ≤ (0 : Int) + d1733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2913, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23896 p hg
    simpa only [d2913, d1733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2913, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23899 p hg
    simpa only [d2913, d1733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23901 (p : Pattern) (guard : d4474 p = 1) : d2914 p ≤ (0 : Int) + d1734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2914, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23895 p hg
    simpa only [d2914, d1734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2914, d1734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23900 p hg
    simpa only [d2914, d1734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23902 (p : Pattern) (guard : d4474 p = 1) : d2915 p ≤ (0 : Int) + d1735 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2915, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23892 p hg
    simpa only [d2915, d1735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2915, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2915, d1735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23903 (p : Pattern) (guard : d4474 p = 1) : d2916 p ≤ (0 : Int) + d1736 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2916, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23902 p hg
    simpa only [d2916, d1736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2916, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23899 p hg
    simpa only [d2916, d1736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23904 (p : Pattern) (guard : d4474 p = 1) : d2917 p ≤ (0 : Int) + d527 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2917, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23886 p hg
    simpa only [d2917, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2917, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2917, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23905 (p : Pattern) (guard : d4474 p = 1) : d2918 p ≤ (0 : Int) + d528 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2918, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23904 p hg
    simpa only [d2918, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2918, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2918, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23906 (p : Pattern) (guard : d4474 p = 1) : d2919 p ≤ (0 : Int) + d1737 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2919, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23903 p hg
    simpa only [d2919, d1737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2919, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23905 p hg
    simpa only [d2919, d1737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23907 (p : Pattern) (guard : d4474 p = 1) : d2920 p ≤ (0 : Int) + d1738 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2920, d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23901 p hg
    simpa only [d2920, d1738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2920, d1738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23906 p hg
    simpa only [d2920, d1738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23908 (p : Pattern) (guard : d4474 p = 1) : d2921 p ≤ (0 : Int) + d1739 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2921, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23890 p hg
    simpa only [d2921, d1739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2921, d1739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23907 p hg
    simpa only [d2921, d1739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23909 (p : Pattern) (guard : d0 p = 1) : d1772 p ≤ (0 : Int) + d335 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23910 (p : Pattern) (guard : d4474 p = 1) : d2895 p ≤ (0 : Int) + d1740 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2895, d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d2895, d1740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2895, d1740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23909 p hg
    simpa only [d4474, d2895, d1740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23911 (p : Pattern) (guard : d4474 p = 1) : d2896 p ≤ (0 : Int) + d1741 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2896, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23910 p hg
    simpa only [d2896, d1741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2896, d1741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16330 p hg
    simpa only [d2896, d1741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23912 (p : Pattern) (guard : d0 p = 1) : d2030 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23913 (p : Pattern) (guard : d4474 p = 1) : d2922 p ≤ (0 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2922, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d4474, d2922, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2922, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23912 p hg
    simpa only [d4474, d2922, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23914 (p : Pattern) (guard : d4474 p = 1) : d2923 p ≤ (0 : Int) + d1747 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2923, d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23913 p hg
    simpa only [d2923, d1747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2923, d1747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16373 p hg
    simpa only [d2923, d1747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23915 (p : Pattern) (guard : d4474 p = 1) : d2924 p ≤ (0 : Int) + d1748 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2924, d1748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23911 p hg
    simpa only [d2924, d1748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2924, d1748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23914 p hg
    simpa only [d2924, d1748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23916 (p : Pattern) (guard : d4474 p = 1) : d2925 p ≤ (0 : Int) + d1749 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2925, d1749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23882 p hg
    simpa only [d2925, d1749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2925, d1749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23887 p hg
    simpa only [d2925, d1749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23917 (p : Pattern) (guard : d4474 p = 1) : d2926 p ≤ (0 : Int) + d1750 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2926, d1750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23915 p hg
    simpa only [d2926, d1750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2926, d1750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23916 p hg
    simpa only [d2926, d1750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23918 (p : Pattern) (guard : d0 p = 1) : d1752 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23919 (p : Pattern) (guard : d4474 p = 1) : d2927 p ≤ (0 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2927, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2022 p hg
    simpa only [d4474, d2927, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2927, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23918 p hg
    simpa only [d4474, d2927, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23920 (p : Pattern) (guard : d4474 p = 1) : d2928 p ≤ (0 : Int) + d1754 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2928, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23919 p hg
    simpa only [d2928, d1754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2928, d1754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16379 p hg
    simpa only [d2928, d1754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23921 (p : Pattern) (guard : d4474 p = 1) : d2929 p ≤ (0 : Int) + d1755 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2929, d1755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23882 p hg
    simpa only [d2929, d1755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2929, d1755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23920 p hg
    simpa only [d2929, d1755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23922 (p : Pattern) (guard : d0 p = 1) : d1729 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23923 (p : Pattern) (guard : d4474 p = 1) : d2930 p ≤ (0 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2930, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2025 p hg
    simpa only [d4474, d2930, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2930, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23922 p hg
    simpa only [d4474, d2930, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23924 (p : Pattern) (guard : d4474 p = 1) : d2931 p ≤ (0 : Int) + d1756 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2931, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23923 p hg
    simpa only [d2931, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2931, d1756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16356 p hg
    simpa only [d2931, d1756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23925 (p : Pattern) (guard : d4474 p = 1) : d2932 p ≤ (0 : Int) + d1757 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2932, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23924 p hg
    simpa only [d2932, d1757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2932, d1757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2932, d1757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23926 (p : Pattern) (guard : d4474 p = 1) : d2933 p ≤ (0 : Int) + d1758 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2933, d1758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23921 p hg
    simpa only [d2933, d1758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2933, d1758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23925 p hg
    simpa only [d2933, d1758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23927 (p : Pattern) (guard : d4474 p = 1) : d2934 p ≤ (0 : Int) + d1759 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2934, d1759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23917 p hg
    simpa only [d2934, d1759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2934, d1759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23926 p hg
    simpa only [d2934, d1759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23928 (p : Pattern) (guard : d0 p = 1) : d1717 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23929 (p : Pattern) (guard : d4474 p = 1) : d2935 p ≤ (0 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d2935, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2017 p hg
    simpa only [d4474, d2935, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d2935, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23928 p hg
    simpa only [d4474, d2935, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23930 (p : Pattern) (guard : d4474 p = 1) : d2936 p ≤ (0 : Int) + d1760 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2936, d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23929 p hg
    simpa only [d2936, d1760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2936, d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2936, d1760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23931 (p : Pattern) (guard : d4474 p = 1) : d2937 p ≤ (0 : Int) + d1761 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2937, d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23894 p hg
    simpa only [d2937, d1761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2937, d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23930 p hg
    simpa only [d2937, d1761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23932 (p : Pattern) (guard : d4474 p = 1) : d2938 p ≤ (0 : Int) + d1762 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2938, d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23899 p hg
    simpa only [d2938, d1762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2938, d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23904 p hg
    simpa only [d2938, d1762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23933 (p : Pattern) (guard : d4474 p = 1) : d2939 p ≤ (0 : Int) + d1763 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2939, d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23931 p hg
    simpa only [d2939, d1763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2939, d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23932 p hg
    simpa only [d2939, d1763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23934 (p : Pattern) (guard : d4474 p = 1) : d2940 p ≤ (0 : Int) + d277 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2940, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23919 p hg
    simpa only [d2940, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2940, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2940, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23935 (p : Pattern) (guard : d4474 p = 1) : d2941 p ≤ (0 : Int) + d1764 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2941, d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23899 p hg
    simpa only [d2941, d1764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2941, d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23934 p hg
    simpa only [d2941, d1764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23936 (p : Pattern) (guard : d4474 p = 1) : d2942 p ≤ (0 : Int) + d538 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2942, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23923 p hg
    simpa only [d2942, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2942, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2942, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23937 (p : Pattern) (guard : d4474 p = 1) : d2943 p ≤ (0 : Int) + d539 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2943, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23936 p hg
    simpa only [d2943, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2943, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16346 p hg
    simpa only [d2943, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23938 (p : Pattern) (guard : d4474 p = 1) : d2944 p ≤ (0 : Int) + d1765 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2944, d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23935 p hg
    simpa only [d2944, d1765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2944, d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23937 p hg
    simpa only [d2944, d1765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23939 (p : Pattern) (guard : d4474 p = 1) : d2945 p ≤ (0 : Int) + d1766 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4474 p = 1 := by simpa only [d2945, d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23933 p hg
    simpa only [d2945, d1766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d2945, d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23938 p hg
    simpa only [d2945, d1766, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
