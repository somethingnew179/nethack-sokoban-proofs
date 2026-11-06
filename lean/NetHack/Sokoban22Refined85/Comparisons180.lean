/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons179
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare25200 (p : Pattern) (guard : d5502 p = 1) : d3112 p ≤ (0 : Int) + d2808 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3112, d2808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25193 p hg
    simpa only [d3112, d2808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3112, d2808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25199 p hg
    simpa only [d3112, d2808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25201 (p : Pattern) (guard : d5502 p = 1) : d3113 p ≤ (0 : Int) + d2809 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3113, d2809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25182 p hg
    simpa only [d3113, d2809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3113, d2809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25200 p hg
    simpa only [d3113, d2809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25202 (p : Pattern) (guard : d5502 p = 1) : d3114 p ≤ (0 : Int) + d2518 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3114, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14835 p hg
    simpa only [d3114, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3114, d2518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17211 p hg
    simpa only [d3114, d2518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25203 (p : Pattern) (guard : d5502 p = 1) : d2049 p ≤ (0 : Int) + d2600 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2049, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17499 p hg
    simpa only [d2049, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2049, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2049, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25204 (p : Pattern) (guard : d5502 p = 1) : d3115 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3115, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25202 p hg
    simpa only [d3115, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3115, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25203 p hg
    simpa only [d3115, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25205 (p : Pattern) (guard : d5502 p = 1) : d2055 p ≤ (0 : Int) + d2600 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2055, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17504 p hg
    simpa only [d2055, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2055, d2600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2055, d2600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25206 (p : Pattern) (guard : d5502 p = 1) : d3116 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3116, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d3116, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3116, d2601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25205 p hg
    simpa only [d3116, d2601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25207 (p : Pattern) (guard : d5502 p = 1) : d3117 p ≤ (0 : Int) + d2601 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25204 p hg
    simpa only [d3117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25206 p hg
    simpa only [d3117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25208 (p : Pattern) (guard : d5502 p = 1) : d3118 p ≤ (0 : Int) + d2810 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3118, d2810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25207 p hg
    simpa only [d3118, d2810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3118, d2810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24997 p hg
    simpa only [d3118, d2810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25209 (p : Pattern) (guard : d5502 p = 1) : d3119 p ≤ (0 : Int) + d2811 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3119, d2811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25208 p hg
    simpa only [d3119, d2811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3119, d2811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24998 p hg
    simpa only [d3119, d2811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25210 (p : Pattern) (guard : d5502 p = 1) : d3120 p ≤ (0 : Int) + d2814 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3120, d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15172 p hg
    simpa only [d3120, d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3120, d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17516 p hg
    simpa only [d3120, d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25211 (p : Pattern) (guard : d5502 p = 1) : d2062 p ≤ (0 : Int) + d2815 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2062, d2815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17516 p hg
    simpa only [d2062, d2815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2062, d2815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2062, d2815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25212 (p : Pattern) (guard : d5502 p = 1) : d3121 p ≤ (0 : Int) + d2816 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3121, d2816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25210 p hg
    simpa only [d3121, d2816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3121, d2816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25211 p hg
    simpa only [d3121, d2816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25213 (p : Pattern) (guard : d5502 p = 1) : d3122 p ≤ (0 : Int) + d2817 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3122, d2817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24986 p hg
    simpa only [d3122, d2817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3122, d2817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25212 p hg
    simpa only [d3122, d2817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25214 (p : Pattern) (guard : d5502 p = 1) : d3123 p ≤ (0 : Int) + d2818 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3123, d2818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25213 p hg
    simpa only [d3123, d2818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3123, d2818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3123, d2818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25215 (p : Pattern) (guard : d5502 p = 1) : d3124 p ≤ (0 : Int) + d2819 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3124, d2819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25214 p hg
    simpa only [d3124, d2819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3124, d2819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3124, d2819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25216 (p : Pattern) (guard : d5502 p = 1) : d3125 p ≤ (0 : Int) + d2820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3125, d2820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25209 p hg
    simpa only [d3125, d2820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3125, d2820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25215 p hg
    simpa only [d3125, d2820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25217 (p : Pattern) (guard : d5502 p = 1) : d2072 p ≤ (0 : Int) + d2543 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2072, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17525 p hg
    simpa only [d2072, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2072, d2543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2072, d2543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25218 (p : Pattern) (guard : d5502 p = 1) : d3126 p ≤ (0 : Int) + d2611 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3126, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24963 p hg
    simpa only [d3126, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3126, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25217 p hg
    simpa only [d3126, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25219 (p : Pattern) (guard : d5502 p = 1) : d3127 p ≤ (0 : Int) + d2611 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25218 p hg
    simpa only [d3127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24994 p hg
    simpa only [d3127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25220 (p : Pattern) (guard : d5502 p = 1) : d3128 p ≤ (0 : Int) + d2821 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3128, d2821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24986 p hg
    simpa only [d3128, d2821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3128, d2821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24959 p hg
    simpa only [d3128, d2821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25221 (p : Pattern) (guard : d5502 p = 1) : d3129 p ≤ (0 : Int) + d2822 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3129, d2822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25219 p hg
    simpa only [d3129, d2822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3129, d2822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25220 p hg
    simpa only [d3129, d2822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25222 (p : Pattern) (guard : d5502 p = 1) : d3130 p ≤ (0 : Int) + d2823 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3130, d2823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25221 p hg
    simpa only [d3130, d2823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3130, d2823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25008 p hg
    simpa only [d3130, d2823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25223 (p : Pattern) (guard : d5502 p = 1) : d3131 p ≤ (0 : Int) + d2824 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3131, d2824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25212 p hg
    simpa only [d3131, d2824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3131, d2824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3131, d2824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25224 (p : Pattern) (guard : d5502 p = 1) : d3132 p ≤ (0 : Int) + d2825 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3132, d2825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25223 p hg
    simpa only [d3132, d2825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3132, d2825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3132, d2825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25225 (p : Pattern) (guard : d5502 p = 1) : d3133 p ≤ (0 : Int) + d2826 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3133, d2826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25224 p hg
    simpa only [d3133, d2826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3133, d2826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3133, d2826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25226 (p : Pattern) (guard : d5502 p = 1) : d3134 p ≤ (0 : Int) + d2827 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3134, d2827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25222 p hg
    simpa only [d3134, d2827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3134, d2827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25225 p hg
    simpa only [d3134, d2827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25227 (p : Pattern) (guard : d5502 p = 1) : d3135 p ≤ (0 : Int) + d2828 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3135, d2828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25216 p hg
    simpa only [d3135, d2828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3135, d2828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25226 p hg
    simpa only [d3135, d2828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25228 (p : Pattern) (guard : d5502 p = 1) : d3136 p ≤ (0 : Int) + d2829 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3136, d2829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25201 p hg
    simpa only [d3136, d2829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3136, d2829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25227 p hg
    simpa only [d3136, d2829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25229 (p : Pattern) (guard : d5502 p = 1) : d3137 p ≤ (0 : Int) + d2830 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3137, d2830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25227 p hg
    simpa only [d3137, d2830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3137, d2830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3137, d2830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25230 (p : Pattern) (guard : d5502 p = 1) : d3138 p ≤ (0 : Int) + d2831 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3138, d2831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25228 p hg
    simpa only [d3138, d2831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3138, d2831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25229 p hg
    simpa only [d3138, d2831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25231 (p : Pattern) (guard : d5502 p = 1) : d3139 p ≤ (0 : Int) + d2832 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3139, d2832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25048 p hg
    simpa only [d3139, d2832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3139, d2832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25230 p hg
    simpa only [d3139, d2832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25232 (p : Pattern) (guard : d5502 p = 1) : d3140 p ≤ (0 : Int) + d2833 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3140, d2833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25035 p hg
    simpa only [d3140, d2833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3140, d2833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25231 p hg
    simpa only [d3140, d2833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25233 (p : Pattern) (guard : d5502 p = 1) : d3141 p ≤ (0 : Int) + d2834 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3141, d2834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25065 p hg
    simpa only [d3141, d2834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3141, d2834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3141, d2834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25234 (p : Pattern) (guard : d5502 p = 1) : d3142 p ≤ (0 : Int) + d2835 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3142, d2835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25091 p hg
    simpa only [d3142, d2835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3142, d2835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25233 p hg
    simpa only [d3142, d2835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25235 (p : Pattern) (guard : d5502 p = 1) : d3143 p ≤ (0 : Int) + d2836 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3143, d2836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25233 p hg
    simpa only [d3143, d2836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3143, d2836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3143, d2836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25236 (p : Pattern) (guard : d5502 p = 1) : d3144 p ≤ (0 : Int) + d2837 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3144, d2837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25234 p hg
    simpa only [d3144, d2837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3144, d2837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25235 p hg
    simpa only [d3144, d2837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25237 (p : Pattern) (guard : d5502 p = 1) : d3145 p ≤ (0 : Int) + d2838 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3145, d2838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25079 p hg
    simpa only [d3145, d2838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3145, d2838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3145, d2838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25238 (p : Pattern) (guard : d5502 p = 1) : d3146 p ≤ (0 : Int) + d2839 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3146, d2839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25099 p hg
    simpa only [d3146, d2839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3146, d2839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25237 p hg
    simpa only [d3146, d2839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25239 (p : Pattern) (guard : d5502 p = 1) : d3147 p ≤ (0 : Int) + d2840 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3147, d2840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25237 p hg
    simpa only [d3147, d2840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3147, d2840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3147, d2840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25240 (p : Pattern) (guard : d5502 p = 1) : d3148 p ≤ (0 : Int) + d2841 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3148, d2841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25238 p hg
    simpa only [d3148, d2841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3148, d2841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25239 p hg
    simpa only [d3148, d2841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25241 (p : Pattern) (guard : d5502 p = 1) : d3149 p ≤ (0 : Int) + d2842 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3149, d2842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25236 p hg
    simpa only [d3149, d2842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3149, d2842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25240 p hg
    simpa only [d3149, d2842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25242 (p : Pattern) (guard : d5502 p = 1) : d3150 p ≤ (0 : Int) + d2843 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3150, d2843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25085 p hg
    simpa only [d3150, d2843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3150, d2843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25241 p hg
    simpa only [d3150, d2843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25243 (p : Pattern) (guard : d5502 p = 1) : d3151 p ≤ (0 : Int) + d2844 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3151, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25120 p hg
    simpa only [d3151, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3151, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3151, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25244 (p : Pattern) (guard : d5502 p = 1) : d3152 p ≤ (0 : Int) + d2845 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3152, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25132 p hg
    simpa only [d3152, d2845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3152, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25243 p hg
    simpa only [d3152, d2845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25245 (p : Pattern) (guard : d5502 p = 1) : d3153 p ≤ (0 : Int) + d2846 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3153, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25243 p hg
    simpa only [d3153, d2846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3153, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3153, d2846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25246 (p : Pattern) (guard : d5502 p = 1) : d3154 p ≤ (0 : Int) + d2847 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3154, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25244 p hg
    simpa only [d3154, d2847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3154, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25245 p hg
    simpa only [d3154, d2847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25247 (p : Pattern) (guard : d5502 p = 1) : d3155 p ≤ (0 : Int) + d2848 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3155, d2848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25246 p hg
    simpa only [d3155, d2848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3155, d2848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25140 p hg
    simpa only [d3155, d2848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25248 (p : Pattern) (guard : d5502 p = 1) : d3156 p ≤ (0 : Int) + d2849 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3156, d2849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25131 p hg
    simpa only [d3156, d2849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3156, d2849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25247 p hg
    simpa only [d3156, d2849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25249 (p : Pattern) (guard : d5502 p = 1) : d3157 p ≤ (0 : Int) + d2850 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3157, d2850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25242 p hg
    simpa only [d3157, d2850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3157, d2850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25248 p hg
    simpa only [d3157, d2850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25250 (p : Pattern) (guard : d5502 p = 1) : d3158 p ≤ (0 : Int) + d2851 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3158, d2851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25248 p hg
    simpa only [d3158, d2851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3158, d2851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25147 p hg
    simpa only [d3158, d2851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25251 (p : Pattern) (guard : d5502 p = 1) : d3159 p ≤ (0 : Int) + d2852 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3159, d2852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25249 p hg
    simpa only [d3159, d2852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3159, d2852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25250 p hg
    simpa only [d3159, d2852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25252 (p : Pattern) (guard : d5502 p = 1) : d3160 p ≤ (0 : Int) + d2686 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3160, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15030 p hg
    simpa only [d3160, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3160, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17397 p hg
    simpa only [d3160, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25253 (p : Pattern) (guard : d5502 p = 1) : d2109 p ≤ (0 : Int) + d2745 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2109, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17562 p hg
    simpa only [d2109, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2109, d2745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2109, d2745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25254 (p : Pattern) (guard : d5502 p = 1) : d3161 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3161, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25252 p hg
    simpa only [d3161, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3161, d2746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25253 p hg
    simpa only [d3161, d2746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25255 (p : Pattern) (guard : d5502 p = 1) : d3162 p ≤ (0 : Int) + d2749 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3162, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25254 p hg
    simpa only [d3162, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3162, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25120 p hg
    simpa only [d3162, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25256 (p : Pattern) (guard : d5502 p = 1) : d3163 p ≤ (0 : Int) + d2750 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3163, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25109 p hg
    simpa only [d3163, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3163, d2750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25255 p hg
    simpa only [d3163, d2750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25257 (p : Pattern) (guard : d5502 p = 1) : d3164 p ≤ (0 : Int) + d2749 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3164, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25115 p hg
    simpa only [d3164, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3164, d2749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25120 p hg
    simpa only [d3164, d2749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25258 (p : Pattern) (guard : d5502 p = 1) : d3165 p ≤ (0 : Int) + d2751 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3165, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25257 p hg
    simpa only [d3165, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3165, d2751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25068 p hg
    simpa only [d3165, d2751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25259 (p : Pattern) (guard : d5502 p = 1) : d3166 p ≤ (0 : Int) + d2752 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3166, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25256 p hg
    simpa only [d3166, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3166, d2752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25258 p hg
    simpa only [d3166, d2752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25260 (p : Pattern) (guard : d5502 p = 1) : d3167 p ≤ (0 : Int) + d2853 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3167, d2853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25097 p hg
    simpa only [d3167, d2853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3167, d2853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25074 p hg
    simpa only [d3167, d2853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25261 (p : Pattern) (guard : d5502 p = 1) : d3168 p ≤ (0 : Int) + d2854 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3168, d2854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25125 p hg
    simpa only [d3168, d2854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3168, d2854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25260 p hg
    simpa only [d3168, d2854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25262 (p : Pattern) (guard : d5502 p = 1) : d3169 p ≤ (0 : Int) + d2855 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3169, d2855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25261 p hg
    simpa only [d3169, d2855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3169, d2855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25237 p hg
    simpa only [d3169, d2855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25263 (p : Pattern) (guard : d5502 p = 1) : d3170 p ≤ (0 : Int) + d2856 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3170, d2856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25126 p hg
    simpa only [d3170, d2856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3170, d2856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3170, d2856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25264 (p : Pattern) (guard : d5502 p = 1) : d3171 p ≤ (0 : Int) + d2857 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3171, d2857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25263 p hg
    simpa only [d3171, d2857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3171, d2857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3171, d2857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25265 (p : Pattern) (guard : d5502 p = 1) : d3172 p ≤ (0 : Int) + d2858 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3172, d2858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25264 p hg
    simpa only [d3172, d2858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3172, d2858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3172, d2858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25266 (p : Pattern) (guard : d5502 p = 1) : d3173 p ≤ (0 : Int) + d2859 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3173, d2859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25262 p hg
    simpa only [d3173, d2859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3173, d2859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25265 p hg
    simpa only [d3173, d2859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25267 (p : Pattern) (guard : d5502 p = 1) : d3174 p ≤ (0 : Int) + d2860 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3174, d2860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25259 p hg
    simpa only [d3174, d2860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3174, d2860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25266 p hg
    simpa only [d3174, d2860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25268 (p : Pattern) (guard : d5502 p = 1) : d3175 p ≤ (0 : Int) + d2703 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d3175, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17336 p hg
    simpa only [d5502, d3175, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d3175, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17334 p hg
    simpa only [d5502, d3175, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25269 (p : Pattern) (guard : d5502 p = 1) : d3176 p ≤ (0 : Int) + d2704 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3176, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17335 p hg
    simpa only [d3176, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3176, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25268 p hg
    simpa only [d3176, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25270 (p : Pattern) (guard : d5502 p = 1) : d3177 p ≤ (0 : Int) + d2725 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3177, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15057 p hg
    simpa only [d3177, d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3177, d2725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25269 p hg
    simpa only [d3177, d2725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25271 (p : Pattern) (guard : d5502 p = 1) : d2126 p ≤ (0 : Int) + d2705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2126, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17581 p hg
    simpa only [d2126, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2126, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2126, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25272 (p : Pattern) (guard : d5502 p = 1) : d3178 p ≤ (0 : Int) + d2753 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3178, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25270 p hg
    simpa only [d3178, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3178, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25271 p hg
    simpa only [d3178, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25273 (p : Pattern) (guard : d5502 p = 1) : d3179 p ≤ (0 : Int) + d2760 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3179, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25254 p hg
    simpa only [d3179, d2760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3179, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25272 p hg
    simpa only [d3179, d2760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25274 (p : Pattern) (guard : d5502 p = 1) : d3180 p ≤ (0 : Int) + d2692 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3180, d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15042 p hg
    simpa only [d3180, d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3180, d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17594 p hg
    simpa only [d3180, d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25275 (p : Pattern) (guard : d5502 p = 1) : d2131 p ≤ (0 : Int) + d2747 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2131, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17588 p hg
    simpa only [d2131, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2131, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2131, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25276 (p : Pattern) (guard : d5502 p = 1) : d3181 p ≤ (0 : Int) + d2748 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3181, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25274 p hg
    simpa only [d3181, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3181, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25275 p hg
    simpa only [d3181, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25277 (p : Pattern) (guard : d5502 p = 1) : d3182 p ≤ (0 : Int) + d2844 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3182, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25276 p hg
    simpa only [d3182, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3182, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3182, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25278 (p : Pattern) (guard : d5502 p = 1) : d3183 p ≤ (0 : Int) + d2845 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3183, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25273 p hg
    simpa only [d3183, d2845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3183, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25277 p hg
    simpa only [d3183, d2845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25279 (p : Pattern) (guard : d5502 p = 1) : d2137 p ≤ (0 : Int) + d2747 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2137, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17594 p hg
    simpa only [d2137, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2137, d2747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2137, d2747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25280 (p : Pattern) (guard : d5502 p = 1) : d3184 p ≤ (0 : Int) + d2748 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3184, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25078 p hg
    simpa only [d3184, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3184, d2748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25279 p hg
    simpa only [d3184, d2748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25281 (p : Pattern) (guard : d5502 p = 1) : d3185 p ≤ (0 : Int) + d2844 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3185, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25280 p hg
    simpa only [d3185, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3185, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3185, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25282 (p : Pattern) (guard : d5502 p = 1) : d3186 p ≤ (0 : Int) + d2846 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3186, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25281 p hg
    simpa only [d3186, d2846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3186, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3186, d2846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25283 (p : Pattern) (guard : d5502 p = 1) : d3187 p ≤ (0 : Int) + d2847 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3187, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25278 p hg
    simpa only [d3187, d2847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3187, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25282 p hg
    simpa only [d3187, d2847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25284 (p : Pattern) (guard : d5502 p = 1) : d3188 p ≤ (0 : Int) + d2861 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3188, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25078 p hg
    simpa only [d3188, d2861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3188, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25074 p hg
    simpa only [d3188, d2861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25285 (p : Pattern) (guard : d5502 p = 1) : d3189 p ≤ (0 : Int) + d2862 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3189, d2862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25284 p hg
    simpa only [d3189, d2862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3189, d2862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25079 p hg
    simpa only [d3189, d2862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25286 (p : Pattern) (guard : d5502 p = 1) : d3190 p ≤ (0 : Int) + d2863 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3190, d2863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25285 p hg
    simpa only [d3190, d2863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3190, d2863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25264 p hg
    simpa only [d3190, d2863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25287 (p : Pattern) (guard : d5502 p = 1) : d3191 p ≤ (0 : Int) + d2864 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3191, d2864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24942 p hg
    simpa only [d3191, d2864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3191, d2864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3191, d2864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25288 (p : Pattern) (guard : d5502 p = 1) : d3192 p ≤ (0 : Int) + d2865 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3192, d2865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25286 p hg
    simpa only [d3192, d2865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3192, d2865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25287 p hg
    simpa only [d3192, d2865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25289 (p : Pattern) (guard : d5502 p = 1) : d3193 p ≤ (0 : Int) + d2866 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3193, d2866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25283 p hg
    simpa only [d3193, d2866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3193, d2866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25288 p hg
    simpa only [d3193, d2866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25290 (p : Pattern) (guard : d5502 p = 1) : d3194 p ≤ (0 : Int) + d2867 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3194, d2867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25267 p hg
    simpa only [d3194, d2867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3194, d2867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25289 p hg
    simpa only [d3194, d2867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25291 (p : Pattern) (guard : d5502 p = 1) : d3195 p ≤ (0 : Int) + d2746 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25115 p hg
    simpa only [d3195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25118 p hg
    simpa only [d3195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25292 (p : Pattern) (guard : d5502 p = 1) : d3196 p ≤ (0 : Int) + d2868 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3196, d2868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25125 p hg
    simpa only [d3196, d2868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3196, d2868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24959 p hg
    simpa only [d3196, d2868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25293 (p : Pattern) (guard : d5502 p = 1) : d3197 p ≤ (0 : Int) + d2869 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3197, d2869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25291 p hg
    simpa only [d3197, d2869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3197, d2869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25292 p hg
    simpa only [d3197, d2869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25294 (p : Pattern) (guard : d5502 p = 1) : d3198 p ≤ (0 : Int) + d2870 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3198, d2870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25293 p hg
    simpa only [d3198, d2870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3198, d2870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25136 p hg
    simpa only [d3198, d2870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25295 (p : Pattern) (guard : d5502 p = 1) : d3199 p ≤ (0 : Int) + d2871 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3199, d2871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25294 p hg
    simpa only [d3199, d2871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3199, d2871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25140 p hg
    simpa only [d3199, d2871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25296 (p : Pattern) (guard : d5502 p = 1) : d2158 p ≤ (0 : Int) + d2705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2158, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17614 p hg
    simpa only [d2158, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2158, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d2158, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25297 (p : Pattern) (guard : d5502 p = 1) : d3200 p ≤ (0 : Int) + d2753 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3200, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25097 p hg
    simpa only [d3200, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3200, d2753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25296 p hg
    simpa only [d3200, d2753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25298 (p : Pattern) (guard : d5502 p = 1) : d3201 p ≤ (0 : Int) + d2753 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25297 p hg
    simpa only [d3201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25125 p hg
    simpa only [d3201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25299 (p : Pattern) (guard : d5502 p = 1) : d3202 p ≤ (0 : Int) + d2872 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3202, d2872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25298 p hg
    simpa only [d3202, d2872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3202, d2872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25243 p hg
    simpa only [d3202, d2872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25300 (p : Pattern) (guard : d5502 p = 1) : d3203 p ≤ (0 : Int) + d2873 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3203, d2873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25299 p hg
    simpa only [d3203, d2873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3203, d2873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25139 p hg
    simpa only [d3203, d2873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25301 (p : Pattern) (guard : d5502 p = 1) : d3204 p ≤ (0 : Int) + d2874 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3204, d2874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24991 p hg
    simpa only [d3204, d2874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3204, d2874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3204, d2874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25302 (p : Pattern) (guard : d5502 p = 1) : d3205 p ≤ (0 : Int) + d2875 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3205, d2875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25301 p hg
    simpa only [d3205, d2875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3205, d2875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3205, d2875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25303 (p : Pattern) (guard : d5502 p = 1) : d3206 p ≤ (0 : Int) + d2876 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3206, d2876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25300 p hg
    simpa only [d3206, d2876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3206, d2876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25302 p hg
    simpa only [d3206, d2876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25304 (p : Pattern) (guard : d5502 p = 1) : d3207 p ≤ (0 : Int) + d2877 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3207, d2877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25295 p hg
    simpa only [d3207, d2877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3207, d2877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25303 p hg
    simpa only [d3207, d2877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25305 (p : Pattern) (guard : d5502 p = 1) : d3208 p ≤ (0 : Int) + d2878 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3208, d2878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25290 p hg
    simpa only [d3208, d2878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3208, d2878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25304 p hg
    simpa only [d3208, d2878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25306 (p : Pattern) (guard : d5502 p = 1) : d3209 p ≤ (0 : Int) + d2879 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3209, d2879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25125 p hg
    simpa only [d3209, d2879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3209, d2879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24990 p hg
    simpa only [d3209, d2879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25307 (p : Pattern) (guard : d5502 p = 1) : d3210 p ≤ (0 : Int) + d2880 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3210, d2880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25291 p hg
    simpa only [d3210, d2880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3210, d2880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25306 p hg
    simpa only [d3210, d2880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25308 (p : Pattern) (guard : d5502 p = 1) : d3211 p ≤ (0 : Int) + d2881 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3211, d2881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25120 p hg
    simpa only [d3211, d2881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3211, d2881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24990 p hg
    simpa only [d3211, d2881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25309 (p : Pattern) (guard : d5502 p = 1) : d3212 p ≤ (0 : Int) + d2882 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3212, d2882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25308 p hg
    simpa only [d3212, d2882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3212, d2882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3212, d2882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25310 (p : Pattern) (guard : d5502 p = 1) : d3213 p ≤ (0 : Int) + d2883 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3213, d2883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25307 p hg
    simpa only [d3213, d2883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3213, d2883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25309 p hg
    simpa only [d3213, d2883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25311 (p : Pattern) (guard : d5502 p = 1) : d3214 p ≤ (0 : Int) + d2884 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3214, d2884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25127 p hg
    simpa only [d3214, d2884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3214, d2884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24959 p hg
    simpa only [d3214, d2884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25312 (p : Pattern) (guard : d5502 p = 1) : d3215 p ≤ (0 : Int) + d2885 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3215, d2885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25311 p hg
    simpa only [d3215, d2885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3215, d2885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3215, d2885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25313 (p : Pattern) (guard : d5502 p = 1) : d3216 p ≤ (0 : Int) + d2886 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3216, d2886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25312 p hg
    simpa only [d3216, d2886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3216, d2886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3216, d2886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25314 (p : Pattern) (guard : d5502 p = 1) : d3217 p ≤ (0 : Int) + d2887 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3217, d2887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25310 p hg
    simpa only [d3217, d2887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3217, d2887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25313 p hg
    simpa only [d3217, d2887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25315 (p : Pattern) (guard : d5502 p = 1) : d3218 p ≤ (0 : Int) + d2888 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3218, d2888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25314 p hg
    simpa only [d3218, d2888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3218, d2888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25303 p hg
    simpa only [d3218, d2888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25316 (p : Pattern) (guard : d5502 p = 1) : d3219 p ≤ (0 : Int) + d2889 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3219, d2889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25315 p hg
    simpa only [d3219, d2889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3219, d2889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21098 p hg
    simpa only [d3219, d2889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25317 (p : Pattern) (guard : d5502 p = 1) : d3220 p ≤ (0 : Int) + d2890 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3220, d2890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25305 p hg
    simpa only [d3220, d2890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3220, d2890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25316 p hg
    simpa only [d3220, d2890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25318 (p : Pattern) (guard : d5502 p = 1) : d3221 p ≤ (0 : Int) + d2891 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3221, d2891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25251 p hg
    simpa only [d3221, d2891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3221, d2891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25317 p hg
    simpa only [d3221, d2891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25319 (p : Pattern) (guard : d5502 p = 1) : d3222 p ≤ (0 : Int) + d2892 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3222, d2892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25035 p hg
    simpa only [d3222, d2892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3222, d2892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25318 p hg
    simpa only [d3222, d2892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25320 (p : Pattern) (guard : d5502 p = 1) : d3223 p ≤ (0 : Int) + d2893 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3223, d2893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25232 p hg
    simpa only [d3223, d2893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3223, d2893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25319 p hg
    simpa only [d3223, d2893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25321 (p : Pattern) (guard : d5502 p = 1) : d3224 p ≤ (0 : Int) + d2894 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d3224, d2894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25163 p hg
    simpa only [d3224, d2894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d3224, d2894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25320 p hg
    simpa only [d3224, d2894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25322 (p : Pattern) (guard : d5540 p = 1) : d14 p ≤ (2 : Int) + d14 p := by
  omega
theorem compare25323 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (2 : Int) + d1770 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25324 (p : Pattern) (guard : d5501 p = 1) : d1771 p ≤ (2 : Int) + d1770 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25323 p hg
    simpa only [d5501, d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24408 p hg
    simpa only [d5501, d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25325 (p : Pattern) (guard : d0 p = 1) : d1770 p ≤ (2 : Int) + d1770 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25326 (p : Pattern) (guard : d5540 p = 1) : d1772 p ≤ (2 : Int) + d1770 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25324 p hg
    simpa only [d5540, d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25325 p hg
    simpa only [d5540, d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25327 (p : Pattern) (guard : d5540 p = 1) : d2895 p ≤ (2 : Int) + d6044 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2895, d6044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25322 p hg
    simpa only [d2895, d6044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2895, d6044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25326 p hg
    simpa only [d2895, d6044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25328 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (2 : Int) + d1684 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25329 (p : Pattern) (guard : d1 p = 1) : d1684 p ≤ (2 : Int) + d1684 p := by
  omega
theorem compare25330 (p : Pattern) (guard : d5501 p = 1) : d1685 p ≤ (2 : Int) + d1684 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25328 p hg
    simpa only [d5501, d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25329 p hg
    simpa only [d5501, d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25331 (p : Pattern) (guard : d0 p = 1) : d1684 p ≤ (2 : Int) + d1684 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25332 (p : Pattern) (guard : d5540 p = 1) : d1686 p ≤ (2 : Int) + d1684 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5501 p = 1 := by simpa only [d5540, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25330 p hg
    simpa only [d5540, d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5540, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25331 p hg
    simpa only [d5540, d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25333 (p : Pattern) (guard : d5540 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare25334 (p : Pattern) (guard : d5540 p = 1) : d1687 p ≤ (2 : Int) + d6045 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d1687, d6045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25332 p hg
    simpa only [d1687, d6045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d1687, d6045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d1687, d6045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25335 (p : Pattern) (guard : d5540 p = 1) : d2896 p ≤ (2 : Int) + d6046 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5540 p = 1 := by simpa only [d2896, d6046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25327 p hg
    simpa only [d2896, d6046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5540 p = 1 := by simpa only [d2896, d6046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25334 p hg
    simpa only [d2896, d6046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25336 (p : Pattern) (guard : d5540 p = 1) : d18 p ≤ (2 : Int) + d18 p := by
  omega
theorem compare25337 (p : Pattern) (guard : d0 p = 1) : d18 p ≤ (2 : Int) + d1795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25338 (p : Pattern) (guard : d5501 p = 1) : d2011 p ≤ (2 : Int) + d1795 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5501, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25337 p hg
    simpa only [d5501, d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d5501, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24637 p hg
    simpa only [d5501, d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25339 (p : Pattern) (guard : d0 p = 1) : d1795 p ≤ (2 : Int) + d1795 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
