/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3220 (p : Pattern) (guard : d4301 p = 1) : d543 p ≤ (0 : Int) + d819 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d543, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3215 p hg
    simpa only [d543, d819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d543, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3219 p hg
    simpa only [d543, d819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3221 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (0 : Int) + d822 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3222 (p : Pattern) (guard : d4302 p = 1) : d544 p ≤ (0 : Int) + d823 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d544, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3220 p hg
    simpa only [d4302, d544, d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d544, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3221 p hg
    simpa only [d4302, d544, d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3223 (p : Pattern) (guard : d4302 p = 1) : d545 p ≤ (0 : Int) + d824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d545, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3211 p hg
    simpa only [d545, d824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d545, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3222 p hg
    simpa only [d545, d824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3224 (p : Pattern) (guard : d0 p = 1) : d28 p ≤ (0 : Int) + d390 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3225 (p : Pattern) (guard : d4299 p = 1) : d29 p ≤ (0 : Int) + d825 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d29, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d4299, d29, d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d29, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3224 p hg
    simpa only [d4299, d29, d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3226 (p : Pattern) (guard : d0 p = 1) : d51 p ≤ (0 : Int) + d826 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3227 (p : Pattern) (guard : d4301 p = 1) : d52 p ≤ (0 : Int) + d827 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d52, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3225 p hg
    simpa only [d4301, d52, d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d52, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3226 p hg
    simpa only [d4301, d52, d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3228 (p : Pattern) (guard : d0 p = 1) : d64 p ≤ (0 : Int) + d394 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3229 (p : Pattern) (guard : d4299 p = 1) : d65 p ≤ (0 : Int) + d828 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d65, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3204 p hg
    simpa only [d4299, d65, d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d65, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3228 p hg
    simpa only [d4299, d65, d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3230 (p : Pattern) (guard : d4301 p = 1) : d76 p ≤ (0 : Int) + d829 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d76, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3229 p hg
    simpa only [d4301, d76, d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d76, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3207 p hg
    simpa only [d4301, d76, d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3231 (p : Pattern) (guard : d4301 p = 1) : d77 p ≤ (0 : Int) + d830 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d77, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3227 p hg
    simpa only [d77, d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d77, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3230 p hg
    simpa only [d77, d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3232 (p : Pattern) (guard : d0 p = 1) : d422 p ≤ (0 : Int) + d833 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3233 (p : Pattern) (guard : d4302 p = 1) : d546 p ≤ (0 : Int) + d834 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d546, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3231 p hg
    simpa only [d4302, d546, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d546, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3232 p hg
    simpa only [d4302, d546, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3234 (p : Pattern) (guard : d0 p = 1) : d28 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3235 (p : Pattern) (guard : d4299 p = 1) : d29 p ≤ (0 : Int) + d831 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d29, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d4299, d29, d831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d29, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3234 p hg
    simpa only [d4299, d29, d831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3236 (p : Pattern) (guard : d4301 p = 1) : d531 p ≤ (0 : Int) + d832 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d531, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3235 p hg
    simpa only [d4301, d531, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d531, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3214 p hg
    simpa only [d4301, d531, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3237 (p : Pattern) (guard : d0 p = 1) : d64 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3238 (p : Pattern) (guard : d4299 p = 1) : d65 p ≤ (0 : Int) + d807 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d65, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3204 p hg
    simpa only [d4299, d65, d807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d65, d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3237 p hg
    simpa only [d4299, d65, d807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3239 (p : Pattern) (guard : d4301 p = 1) : d542 p ≤ (0 : Int) + d812 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d542, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3238 p hg
    simpa only [d4301, d542, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d542, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3218 p hg
    simpa only [d4301, d542, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3240 (p : Pattern) (guard : d4301 p = 1) : d543 p ≤ (0 : Int) + d833 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d543, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3236 p hg
    simpa only [d543, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d543, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3239 p hg
    simpa only [d543, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3241 (p : Pattern) (guard : d4302 p = 1) : d547 p ≤ (0 : Int) + d835 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d547, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3240 p hg
    simpa only [d4302, d547, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d547, d835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4302, d547, d835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3242 (p : Pattern) (guard : d4302 p = 1) : d548 p ≤ (0 : Int) + d836 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d548, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3233 p hg
    simpa only [d548, d836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d548, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3241 p hg
    simpa only [d548, d836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3243 (p : Pattern) (guard : d4302 p = 1) : d549 p ≤ (0 : Int) + d837 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d549, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3223 p hg
    simpa only [d549, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d549, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3242 p hg
    simpa only [d549, d837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3244 (p : Pattern) (guard : d0 p = 1) : d28 p ≤ (0 : Int) + d372 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3245 (p : Pattern) (guard : d4299 p = 1) : d29 p ≤ (0 : Int) + d838 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d29, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d4299, d29, d838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d29, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3244 p hg
    simpa only [d4299, d29, d838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3246 (p : Pattern) (guard : d4301 p = 1) : d52 p ≤ (0 : Int) + d839 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d52, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3245 p hg
    simpa only [d4301, d52, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d52, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3226 p hg
    simpa only [d4301, d52, d839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3247 (p : Pattern) (guard : d0 p = 1) : d64 p ≤ (0 : Int) + d390 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3248 (p : Pattern) (guard : d4299 p = 1) : d65 p ≤ (0 : Int) + d840 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d65, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3204 p hg
    simpa only [d4299, d65, d840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d65, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3247 p hg
    simpa only [d4299, d65, d840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3249 (p : Pattern) (guard : d4301 p = 1) : d76 p ≤ (0 : Int) + d841 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d76, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3248 p hg
    simpa only [d4301, d76, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d76, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3207 p hg
    simpa only [d4301, d76, d841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3250 (p : Pattern) (guard : d4301 p = 1) : d77 p ≤ (0 : Int) + d842 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d77, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3246 p hg
    simpa only [d77, d842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d77, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3249 p hg
    simpa only [d77, d842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3251 (p : Pattern) (guard : d0 p = 1) : d439 p ≤ (0 : Int) + d845 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3252 (p : Pattern) (guard : d4302 p = 1) : d550 p ≤ (0 : Int) + d846 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d550, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3250 p hg
    simpa only [d4302, d550, d846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d550, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3251 p hg
    simpa only [d4302, d550, d846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3253 (p : Pattern) (guard : d0 p = 1) : d28 p ≤ (0 : Int) + d394 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3254 (p : Pattern) (guard : d4299 p = 1) : d29 p ≤ (0 : Int) + d803 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d29, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3199 p hg
    simpa only [d4299, d29, d803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d29, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3253 p hg
    simpa only [d4299, d29, d803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3255 (p : Pattern) (guard : d4301 p = 1) : d531 p ≤ (0 : Int) + d806 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d531, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3254 p hg
    simpa only [d4301, d531, d806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d531, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3214 p hg
    simpa only [d4301, d531, d806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3256 (p : Pattern) (guard : d4301 p = 1) : d543 p ≤ (0 : Int) + d813 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d543, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3255 p hg
    simpa only [d543, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d543, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3239 p hg
    simpa only [d543, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3257 (p : Pattern) (guard : d0 p = 1) : d441 p ≤ (0 : Int) + d822 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3258 (p : Pattern) (guard : d4302 p = 1) : d551 p ≤ (0 : Int) + d847 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d551, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3256 p hg
    simpa only [d4302, d551, d847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d551, d847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3257 p hg
    simpa only [d4302, d551, d847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3259 (p : Pattern) (guard : d4302 p = 1) : d552 p ≤ (0 : Int) + d848 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d552, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3252 p hg
    simpa only [d552, d848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d552, d848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3258 p hg
    simpa only [d552, d848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3260 (p : Pattern) (guard : d4301 p = 1) : d52 p ≤ (0 : Int) + d849 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d52, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3213 p hg
    simpa only [d4301, d52, d849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d52, d849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3226 p hg
    simpa only [d4301, d52, d849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3261 (p : Pattern) (guard : d4301 p = 1) : d76 p ≤ (0 : Int) + d850 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d76, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3217 p hg
    simpa only [d4301, d76, d850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d76, d850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3207 p hg
    simpa only [d4301, d76, d850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3262 (p : Pattern) (guard : d4301 p = 1) : d77 p ≤ (0 : Int) + d851 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d77, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3260 p hg
    simpa only [d77, d851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d77, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3261 p hg
    simpa only [d77, d851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3263 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (0 : Int) + d833 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3264 (p : Pattern) (guard : d4302 p = 1) : d553 p ≤ (0 : Int) + d852 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d553, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3262 p hg
    simpa only [d4302, d553, d852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d553, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3263 p hg
    simpa only [d4302, d553, d852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3265 (p : Pattern) (guard : d4302 p = 1) : d554 p ≤ (0 : Int) + d853 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d554, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3264 p hg
    simpa only [d554, d853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d554, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3241 p hg
    simpa only [d554, d853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3266 (p : Pattern) (guard : d4302 p = 1) : d555 p ≤ (0 : Int) + d854 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d555, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3259 p hg
    simpa only [d555, d854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d555, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3265 p hg
    simpa only [d555, d854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3267 (p : Pattern) (guard : d4302 p = 1) : d556 p ≤ (0 : Int) + d855 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d556, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3243 p hg
    simpa only [d556, d855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d556, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3266 p hg
    simpa only [d556, d855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3268 (p : Pattern) (guard : d1 p = 1) : d111 p ≤ (0 : Int) + d111 p := by
  omega
theorem compare3269 (p : Pattern) (guard : d0 p = 1) : d113 p ≤ (0 : Int) + d372 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3270 (p : Pattern) (guard : d4299 p = 1) : d114 p ≤ (0 : Int) + d856 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d114, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3268 p hg
    simpa only [d4299, d114, d856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d114, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3269 p hg
    simpa only [d4299, d114, d856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3271 (p : Pattern) (guard : d0 p = 1) : d130 p ≤ (0 : Int) + d858 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3272 (p : Pattern) (guard : d4301 p = 1) : d131 p ≤ (0 : Int) + d859 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d131, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3270 p hg
    simpa only [d4301, d131, d859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d131, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3271 p hg
    simpa only [d4301, d131, d859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3273 (p : Pattern) (guard : d1 p = 1) : d135 p ≤ (0 : Int) + d135 p := by
  omega
theorem compare3274 (p : Pattern) (guard : d0 p = 1) : d137 p ≤ (0 : Int) + d390 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3275 (p : Pattern) (guard : d4299 p = 1) : d138 p ≤ (0 : Int) + d860 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d138, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3273 p hg
    simpa only [d4299, d138, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d138, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3274 p hg
    simpa only [d4299, d138, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3276 (p : Pattern) (guard : d0 p = 1) : d145 p ≤ (0 : Int) + d865 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3277 (p : Pattern) (guard : d4301 p = 1) : d146 p ≤ (0 : Int) + d866 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d146, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3275 p hg
    simpa only [d4301, d146, d866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d146, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3276 p hg
    simpa only [d4301, d146, d866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3278 (p : Pattern) (guard : d4301 p = 1) : d147 p ≤ (0 : Int) + d867 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d147, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3272 p hg
    simpa only [d147, d867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d147, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3277 p hg
    simpa only [d147, d867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3279 (p : Pattern) (guard : d0 p = 1) : d439 p ≤ (0 : Int) + d877 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3280 (p : Pattern) (guard : d4302 p = 1) : d557 p ≤ (0 : Int) + d878 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d557, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3278 p hg
    simpa only [d4302, d557, d878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d557, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3279 p hg
    simpa only [d4302, d557, d878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3281 (p : Pattern) (guard : d0 p = 1) : d113 p ≤ (0 : Int) + d394 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3282 (p : Pattern) (guard : d4299 p = 1) : d114 p ≤ (0 : Int) + d879 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d114, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3268 p hg
    simpa only [d4299, d114, d879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d114, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3281 p hg
    simpa only [d4299, d114, d879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3283 (p : Pattern) (guard : d0 p = 1) : d568 p ≤ (0 : Int) + d870 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3284 (p : Pattern) (guard : d4301 p = 1) : d569 p ≤ (0 : Int) + d880 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d569, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3282 p hg
    simpa only [d4301, d569, d880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d569, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3283 p hg
    simpa only [d4301, d569, d880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3285 (p : Pattern) (guard : d0 p = 1) : d137 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3286 (p : Pattern) (guard : d4299 p = 1) : d138 p ≤ (0 : Int) + d872 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d138, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3273 p hg
    simpa only [d4299, d138, d872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d138, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3285 p hg
    simpa only [d4299, d138, d872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3287 (p : Pattern) (guard : d0 p = 1) : d577 p ≤ (0 : Int) + d875 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3288 (p : Pattern) (guard : d4301 p = 1) : d578 p ≤ (0 : Int) + d876 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d578, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3286 p hg
    simpa only [d4301, d578, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d578, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3287 p hg
    simpa only [d4301, d578, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3289 (p : Pattern) (guard : d4301 p = 1) : d579 p ≤ (0 : Int) + d881 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d579, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3284 p hg
    simpa only [d579, d881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d579, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3288 p hg
    simpa only [d579, d881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3290 (p : Pattern) (guard : d4302 p = 1) : d580 p ≤ (0 : Int) + d882 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d580, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3289 p hg
    simpa only [d4302, d580, d882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d580, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2846 p hg
    simpa only [d4302, d580, d882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3291 (p : Pattern) (guard : d4302 p = 1) : d581 p ≤ (0 : Int) + d883 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d581, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3280 p hg
    simpa only [d581, d883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d581, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3290 p hg
    simpa only [d581, d883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3292 (p : Pattern) (guard : d0 p = 1) : d113 p ≤ (0 : Int) + d403 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3293 (p : Pattern) (guard : d4299 p = 1) : d114 p ≤ (0 : Int) + d884 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d114, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3268 p hg
    simpa only [d4299, d114, d884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d114, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3292 p hg
    simpa only [d4299, d114, d884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3294 (p : Pattern) (guard : d4301 p = 1) : d131 p ≤ (0 : Int) + d885 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d131, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3293 p hg
    simpa only [d4301, d131, d885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d131, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3271 p hg
    simpa only [d4301, d131, d885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3295 (p : Pattern) (guard : d0 p = 1) : d137 p ≤ (0 : Int) + d375 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3296 (p : Pattern) (guard : d4299 p = 1) : d138 p ≤ (0 : Int) + d886 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d138, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3273 p hg
    simpa only [d4299, d138, d886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d138, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3295 p hg
    simpa only [d4299, d138, d886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3297 (p : Pattern) (guard : d4301 p = 1) : d146 p ≤ (0 : Int) + d887 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d146, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3296 p hg
    simpa only [d4301, d146, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d146, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3276 p hg
    simpa only [d4301, d146, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3298 (p : Pattern) (guard : d4301 p = 1) : d147 p ≤ (0 : Int) + d888 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d147, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3294 p hg
    simpa only [d147, d888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d147, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3297 p hg
    simpa only [d147, d888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3299 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (0 : Int) + d891 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3300 (p : Pattern) (guard : d4302 p = 1) : d582 p ≤ (0 : Int) + d892 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d582, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3298 p hg
    simpa only [d4302, d582, d892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d582, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3299 p hg
    simpa only [d4302, d582, d892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3301 (p : Pattern) (guard : d0 p = 1) : d113 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3302 (p : Pattern) (guard : d4299 p = 1) : d114 p ≤ (0 : Int) + d889 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d114, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3268 p hg
    simpa only [d4299, d114, d889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d114, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3301 p hg
    simpa only [d4299, d114, d889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3303 (p : Pattern) (guard : d4301 p = 1) : d569 p ≤ (0 : Int) + d890 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d569, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3302 p hg
    simpa only [d4301, d569, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d569, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3283 p hg
    simpa only [d4301, d569, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3304 (p : Pattern) (guard : d4301 p = 1) : d579 p ≤ (0 : Int) + d891 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d579, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3303 p hg
    simpa only [d579, d891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d579, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3288 p hg
    simpa only [d579, d891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3305 (p : Pattern) (guard : d4302 p = 1) : d583 p ≤ (0 : Int) + d893 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d583, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3304 p hg
    simpa only [d4302, d583, d893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d583, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4302, d583, d893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3306 (p : Pattern) (guard : d4302 p = 1) : d584 p ≤ (0 : Int) + d894 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d584, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3300 p hg
    simpa only [d584, d894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d584, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3305 p hg
    simpa only [d584, d894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3307 (p : Pattern) (guard : d4302 p = 1) : d585 p ≤ (0 : Int) + d895 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d585, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3291 p hg
    simpa only [d585, d895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d585, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3306 p hg
    simpa only [d585, d895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3308 (p : Pattern) (guard : d4302 p = 1) : d586 p ≤ (0 : Int) + d896 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d586, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3243 p hg
    simpa only [d586, d896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d586, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3307 p hg
    simpa only [d586, d896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3309 (p : Pattern) (guard : d4302 p = 1) : d587 p ≤ (0 : Int) + d897 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d587, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3267 p hg
    simpa only [d587, d897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d587, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3308 p hg
    simpa only [d587, d897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3310 (p : Pattern) (guard : d0 p = 1) : d412 p ≤ (0 : Int) + d906 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3311 (p : Pattern) (guard : d4302 p = 1) : d553 p ≤ (0 : Int) + d907 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d553, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3262 p hg
    simpa only [d4302, d553, d907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d553, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3310 p hg
    simpa only [d4302, d553, d907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3312 (p : Pattern) (guard : d1 p = 1) : d188 p ≤ (0 : Int) + d188 p := by
  omega
theorem compare3313 (p : Pattern) (guard : d0 p = 1) : d80 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3314 (p : Pattern) (guard : d4299 p = 1) : d189 p ≤ (0 : Int) + d898 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d189, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3312 p hg
    simpa only [d4299, d189, d898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d189, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3313 p hg
    simpa only [d4299, d189, d898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3315 (p : Pattern) (guard : d0 p = 1) : d595 p ≤ (0 : Int) + d900 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3316 (p : Pattern) (guard : d4301 p = 1) : d596 p ≤ (0 : Int) + d901 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d596, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3314 p hg
    simpa only [d4301, d596, d901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d596, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3315 p hg
    simpa only [d4301, d596, d901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3317 (p : Pattern) (guard : d1 p = 1) : d199 p ≤ (0 : Int) + d199 p := by
  omega
theorem compare3318 (p : Pattern) (guard : d0 p = 1) : d84 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3319 (p : Pattern) (guard : d4299 p = 1) : d200 p ≤ (0 : Int) + d902 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d200, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3317 p hg
    simpa only [d4299, d200, d902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d200, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3318 p hg
    simpa only [d4299, d200, d902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3320 (p : Pattern) (guard : d0 p = 1) : d603 p ≤ (0 : Int) + d904 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3321 (p : Pattern) (guard : d4301 p = 1) : d604 p ≤ (0 : Int) + d905 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d604, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3319 p hg
    simpa only [d4301, d604, d905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d604, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3320 p hg
    simpa only [d4301, d604, d905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3322 (p : Pattern) (guard : d4301 p = 1) : d605 p ≤ (0 : Int) + d906 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d605, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3316 p hg
    simpa only [d605, d906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d605, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3321 p hg
    simpa only [d605, d906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3323 (p : Pattern) (guard : d4302 p = 1) : d606 p ≤ (0 : Int) + d908 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d606, d908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3322 p hg
    simpa only [d4302, d606, d908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d606, d908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4302, d606, d908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3324 (p : Pattern) (guard : d4302 p = 1) : d607 p ≤ (0 : Int) + d909 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d607, d909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3311 p hg
    simpa only [d607, d909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d607, d909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3323 p hg
    simpa only [d607, d909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3325 (p : Pattern) (guard : d4302 p = 1) : d608 p ≤ (0 : Int) + d910 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d608, d910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3259 p hg
    simpa only [d608, d910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d608, d910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3324 p hg
    simpa only [d608, d910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3326 (p : Pattern) (guard : d4302 p = 1) : d609 p ≤ (0 : Int) + d911 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d609, d911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3243 p hg
    simpa only [d609, d911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d609, d911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3325 p hg
    simpa only [d609, d911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3327 (p : Pattern) (guard : d1 p = 1) : d212 p ≤ (0 : Int) + d212 p := by
  omega
theorem compare3328 (p : Pattern) (guard : d0 p = 1) : d213 p ≤ (0 : Int) + d451 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3329 (p : Pattern) (guard : d4299 p = 1) : d214 p ≤ (0 : Int) + d912 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d214, d912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3327 p hg
    simpa only [d4299, d214, d912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d214, d912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3328 p hg
    simpa only [d4299, d214, d912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3330 (p : Pattern) (guard : d0 p = 1) : d218 p ≤ (0 : Int) + d865 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3331 (p : Pattern) (guard : d4301 p = 1) : d219 p ≤ (0 : Int) + d913 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d219, d913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3329 p hg
    simpa only [d4301, d219, d913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d219, d913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3330 p hg
    simpa only [d4301, d219, d913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3332 (p : Pattern) (guard : d4301 p = 1) : d220 p ≤ (0 : Int) + d914 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d220, d914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3272 p hg
    simpa only [d220, d914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d220, d914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3331 p hg
    simpa only [d220, d914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3333 (p : Pattern) (guard : d0 p = 1) : d457 p ≤ (0 : Int) + d917 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3334 (p : Pattern) (guard : d4302 p = 1) : d610 p ≤ (0 : Int) + d918 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d610, d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3332 p hg
    simpa only [d4302, d610, d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d610, d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3333 p hg
    simpa only [d4302, d610, d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3335 (p : Pattern) (guard : d0 p = 1) : d213 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3336 (p : Pattern) (guard : d4299 p = 1) : d214 p ≤ (0 : Int) + d915 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d214, d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3327 p hg
    simpa only [d4299, d214, d915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d214, d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3335 p hg
    simpa only [d4299, d214, d915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3337 (p : Pattern) (guard : d0 p = 1) : d614 p ≤ (0 : Int) + d875 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3338 (p : Pattern) (guard : d4301 p = 1) : d615 p ≤ (0 : Int) + d916 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d615, d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3336 p hg
    simpa only [d4301, d615, d916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d615, d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3337 p hg
    simpa only [d4301, d615, d916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3339 (p : Pattern) (guard : d4301 p = 1) : d616 p ≤ (0 : Int) + d919 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d616, d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3284 p hg
    simpa only [d616, d919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d616, d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3338 p hg
    simpa only [d616, d919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3340 (p : Pattern) (guard : d4302 p = 1) : d617 p ≤ (0 : Int) + d920 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d617, d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3339 p hg
    simpa only [d4302, d617, d920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d617, d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2846 p hg
    simpa only [d4302, d617, d920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3341 (p : Pattern) (guard : d4302 p = 1) : d618 p ≤ (0 : Int) + d921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4302 p = 1 := by simpa only [d618, d921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3334 p hg
    simpa only [d618, d921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4302 p = 1 := by simpa only [d618, d921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3340 p hg
    simpa only [d618, d921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3342 (p : Pattern) (guard : d0 p = 1) : d280 p ≤ (0 : Int) + d923 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3343 (p : Pattern) (guard : d4301 p = 1) : d281 p ≤ (0 : Int) + d924 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d281, d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3293 p hg
    simpa only [d4301, d281, d924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d281, d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3342 p hg
    simpa only [d4301, d281, d924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3344 (p : Pattern) (guard : d0 p = 1) : d288 p ≤ (0 : Int) + d927 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3345 (p : Pattern) (guard : d4301 p = 1) : d289 p ≤ (0 : Int) + d928 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d289, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3336 p hg
    simpa only [d4301, d289, d928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d289, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3344 p hg
    simpa only [d4301, d289, d928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3346 (p : Pattern) (guard : d4301 p = 1) : d290 p ≤ (0 : Int) + d929 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d290, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3343 p hg
    simpa only [d290, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d290, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3345 p hg
    simpa only [d290, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3347 (p : Pattern) (guard : d0 p = 1) : d473 p ≤ (0 : Int) + d936 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3348 (p : Pattern) (guard : d4302 p = 1) : d619 p ≤ (0 : Int) + d937 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d4302, d619, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3346 p hg
    simpa only [d4302, d619, d937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4302, d619, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3347 p hg
    simpa only [d4302, d619, d937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3349 (p : Pattern) (guard : d1 p = 1) : d253 p ≤ (0 : Int) + d253 p := by
  omega
theorem compare3350 (p : Pattern) (guard : d0 p = 1) : d255 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3351 (p : Pattern) (guard : d4299 p = 1) : d256 p ≤ (0 : Int) + d938 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d256, d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3349 p hg
    simpa only [d4299, d256, d938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d256, d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3350 p hg
    simpa only [d4299, d256, d938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3352 (p : Pattern) (guard : d0 p = 1) : d630 p ≤ (0 : Int) + d940 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3353 (p : Pattern) (guard : d4301 p = 1) : d631 p ≤ (0 : Int) + d941 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d631, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3351 p hg
    simpa only [d4301, d631, d941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d631, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3352 p hg
    simpa only [d4301, d631, d941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3354 (p : Pattern) (guard : d1 p = 1) : d245 p ≤ (0 : Int) + d245 p := by
  omega
theorem compare3355 (p : Pattern) (guard : d0 p = 1) : d154 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3356 (p : Pattern) (guard : d4299 p = 1) : d246 p ≤ (0 : Int) + d931 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4299, d246, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3354 p hg
    simpa only [d4299, d246, d931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4299, d246, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3355 p hg
    simpa only [d4299, d246, d931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3357 (p : Pattern) (guard : d0 p = 1) : d644 p ≤ (0 : Int) + d934 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3358 (p : Pattern) (guard : d4301 p = 1) : d645 p ≤ (0 : Int) + d935 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d645, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3356 p hg
    simpa only [d4301, d645, d935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d645, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3357 p hg
    simpa only [d4301, d645, d935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3359 (p : Pattern) (guard : d4301 p = 1) : d646 p ≤ (0 : Int) + d942 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4301 p = 1 := by simpa only [d646, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3353 p hg
    simpa only [d646, d942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4301 p = 1 := by simpa only [d646, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3358 p hg
    simpa only [d646, d942, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
